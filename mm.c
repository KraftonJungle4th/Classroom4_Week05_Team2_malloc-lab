/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * ----------
 * mm-naive.c - 가장 빠르고 메모리 효율이 가장 낮은 malloc 패키지입니다.
 *
 * 이 순진한 접근 방식에서는 단순히 brk 포인터를 증가시켜 블록을 할당합니다.
 * 블록은 순수한 페이로드입니다. 헤더나 푸터가 없습니다.
 * 블록은 합쳐지거나 재사용되지 않습니다.
 * 재할당은 mm_malloc과 mm_free를 사용해 직접 구현됩니다.
 *
 * 학생 참고 사항: 이 헤더 코멘트는 솔루션에 대한 높은 수준의
 * 설명을 제공하는 자신만의 헤더 코멘트로 대체하세요.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Classroom4_Week05_Team2_malloc-lab",
    /* First member's full name */
    "KraftonJungle4th",
    /* First member's email address */
    "jungle@krafton.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 정렬을 위한 상수를 정의(8바이트로 정렬을 하겠다.)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 주어진 크기를 정렬에 맞게 조정하는 매크로

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 자료형의 크기를 정렬에 맞게 조정하는 매크로

#define WSIZE 4             // 워드의 크기를 바이트 단위로 정의
#define DSIZE 8             // 더블 워드의 크기를 바이트 단위로 정의
#define CHUNKSIZE (1 << 12) // 초기 힙 확장에 사용되는 정크 크기를 정의 [1_000_000_000_000]
#define SEGREGATED_SIZE (20)// segregated list의 class 개수
/*주어진 두 값 중 큰 값을 반환하는 매크로*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/*메모리 블록의 크기와 할당 비트를 결합하여 헤더 및 풋터에 저장할 값을 반환하는 매크로*/
#define PACK(size, alloc) ((size) | (alloc))

/*p가 가리키는 메모리를 unsigned int로 캐스팅한 뒤 해당 위치의 값을 반환
p가 가리키는 메모리를 unsigned int로 캐스팅한 뒤 해당 위치에 val값을 저장 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*주소 p에 있는 헤더 또는 풋터의 크기를 반환, 할당 비트를 제외하고 나머지 비트를 반환
주소 p에 있는 헤더 또는 풋터의 할당 비트를 반환, 할당 상태를 나타냄*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*주어진 블록 포인터 bp에 대한 헤더 주소를 반환, 주소 bp에서 워드 크기만큼 뺀 주소를 반환*/
#define HDRP(bp) ((char *)(bp)-WSIZE)

/*현재 블록의 이전 블록 헤더로부터 크기를 읽어와 현재 블록의 끝 주소 다음을 반환
현재 블록의 이전 블록의 풋터로부터 크기를 읽어와 이전 블록의 시작 주소를 반환*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static char *heap_listp;                   // 가용 리스트의 시작을 나타내는 포인터
static void *coalesce(void *bp);           // 주변의 가용 블록을 병합하여 하나의 블록으로 만드는 함수를 선언
static void *extend_heap(size_t words);    // 힙을 확장하는 함수를 선언
static void *find_fit(size_t asize);       // 요청된 크기에 맞는 가용 블록을 탐색하는 함수를 선언
static void place(void *bp, size_t aszie); // 할당된 메모리 블록을 가용 리스트에서 제거하고 요청된 크기로 분할하는 함수를 선언
static void splice_free_block(void *bp);   // 가용 리스트에서 제거
static void add_free_block(void *bp);      // 가용 리스트에 추가
static int get_class(size_t size);

int mm_init(void)
{
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);                                                    // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                             // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치
    heap_listp += (2 * WSIZE);
    if (extend_heap(4) == NULL)                  //자주 사용되는 작은 블럭이 잘 처리되어 점수가 오름!!
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t asize = 16;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    while (asize < size + DSIZE)
    {
        asize <<= 1;
    }
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}

// mm_free - 사용하지 않을 블록을 해제합니다.
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

// mm_realloc - mm_malloc 및 mm_free로 간단하게 구현합니다.
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
    return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    void *newptr;

    // 새로운 메모리 블록 할당
    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사

    // 실제 복사할 데이터 크기는 이전 블록 크기와 요청된 새 블록 크기 중 작은 값
    if (size < copySize)
        copySize = size;

    // 데이터를 새 블록으로 복사
    memcpy(newptr, ptr, copySize);

    // 이전 블록 해제
    mm_free(ptr);

    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 확장할 크기를 정렬 요구 사항에 맞게 조정
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새로 확장된 영역의 프리 블록 헤더와 푸터, 그리고 새 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 프리 블록 헤더
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    // 인접한 프리 블록과의 병합을 시도하여 메모리 단편화 감소
    // 코얼레스 (코알라, 코머시기)
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    add_free_block(bp);                                      // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                       // 반환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 1) * WSIZE; // 실제 메모리 블록들이 시작하는 위치
    void *left_buddyp;                                       // 왼쪽 버디의 bp
    void *right_buddyp;                                      // 오른쪽 버디의 bp

    while (1)
    {
        // 좌우 버디의 bp 파악
        if ((bp - root) & csize) // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
        {
            left_buddyp = bp - csize;
            right_buddyp = bp;
        }
        else
        {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }

        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp)) == GET_SIZE(HDRP(right_buddyp)))
        {
            splice_free_block(left_buddyp); // 양쪽 버디를 모두 가용 리스트에서 제거
            splice_free_block(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize, 0)); // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            add_free_block(left_buddyp);            // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        }
        else
            break;
    }
    return bp;
}


static void *find_fit(size_t asize)
{
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                return bp;
            bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
        }
        class += 1;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp);             // free_list에서 해당 블록 제거
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 알아냄

    while (asize != csize) // 사용하려는 asize와 블록의 크기 csize가 다르면
    {
        csize >>= 1;                           // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize, 0)); // 뒷부분을 가용 블록으로 변경
        add_free_block(bp + csize);            // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize, 1)); // 크기가 같아지면 해당 블록 사용 처리
}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

// 적합한 가용 리스트를 찾아서 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);     // bp의 해당 가용 리스트의 루트가 가리키던 블록
    if (GET_ROOT(class) != NULL)        // list에 블록이 존재했을 경우만
        GET_PRED(GET_ROOT(class)) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    GET_ROOT(class) = bp;
}

// 적합한 가용 리스트를 찾는 함수
int get_class(size_t size)
{
    int next_power_of_2 = 1;
    int class = 0;
    while (next_power_of_2 < size && class + 1 < SEGREGATED_SIZE)
    {
        next_power_of_2 <<= 1;
        class ++;
    }

    return class;
}