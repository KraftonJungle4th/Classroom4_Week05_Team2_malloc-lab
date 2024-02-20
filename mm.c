#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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
#define CHUNKSIZE (1 << 12) // 초기 힙 확장에 사용되는 정크 크기를 정의 [2의 12승 (4096)]

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

/*주어진 블록 포인터 bp에 대한 헤더 주소를 반환, 주소 bp에서 워드 크기만큼 뺀 주소를 반환
헤더 주소에서 해당 블록의 크기를 구한 뒤 더블 워드 크기를 빼서 풋터의 주소를 반환*/
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*현재 블록의 이전 블록 헤더로부터 크기를 읽어와 현재 블록의 끝 주소 다음을 반환
현재 블록의 이전 블록의 풋터로부터 크기를 읽어와 이전 블록의 시작 주소를 반환*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// ----------
// 가정: 최대 12개의 사이즈 클래스가 있음
#define MAX_SIZE_CLASS 12

// 다음 가용 블록의 포인터를 가져오는 매크로
#define GET_NEXT_FREEBLK(bp) (*(char **)(bp + WSIZE))

// 이전 가용 블록의 포인터를 가져오는 매크로
#define GET_PREV_FREEBLK(bp) (*(char **)(bp))

// 다음 가용 블록의 포인터를 설정하는 매크로
#define SET_NEXT_FREEBLK(bp, next_bp) (GET_NEXT_FREEBLK(bp) = next_bp)

// 이전 가용 블록의 포인터를 설정하는 매크로
#define SET_PREV_FREEBLK(bp, prev_bp) (GET_PREV_FREEBLK(bp) = prev_bp)

static void *heap_listp;                    // 가용 리스트의 시작을 나타내는 포인터
static void *seg_free_list[MAX_SIZE_CLASS]; // 각 사이즈 클래스별 free list의 헤드를 저장하는 배열
// 사이즈 클래스 분류 기준 예시 (간단화된 버전)
static int size_classes[MAX_SIZE_CLASS] = {4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192};

// 요청된 크기에 맞는 가장 적합한 free block을 찾는 함수
// Seglist를 순회하여 적절한 크기의 블록을 찾음
static void *find_fit(size_t size);

// 할당된 블록에 메모리를 할당
// 필요하다면 남은 부분을 분할하여 free list에 추가
static void place(void *bp, size_t asize);

static int find_class_index(size_t size);

// Free block을 적절한 seglist에 삽입하는 함수
// Free 또는 Coalesce 과정에서 사용
static void add_block_to_seglist(void *bp, size_t size);

// Free list에서 특정 블록을 제거하는 함수. 할당 과정에서 사용
static void remove_block_from_seglist(void *bp);

static void *extend_heap(size_t words);

// 인접한 free block을 병합하는 기존 함수를 seglist 방식에 맞게 조정
// 병합된 블록을 적절한 seglist에 재배치
static void *coalesce(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 1. seg_free_list 초기화
    for (int i = 0; i < MAX_SIZE_CLASS; i++)
    {
        seg_free_list[i] = NULL;
    }

    // 2. 초기 힙 영역 설정
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);                            // 패딩 블록
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더

    heap_listp += (2 * WSIZE);

    // 3. 초기 가용 블록 생성을 위한 힙 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
// 메모리 블록을 할당하는 함수
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 크기
    size_t extendsize; // 필요한 경우 힙을 확장할 크기
    char *bp;

    // 요청된 크기가 0이면 할당하지 않음
    if (size == 0)
    {
        return NULL;
    }

    // 블록 크기를 조정 (예: 헤더와 푸터 크기 포함)
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // 적절한 사이즈 클래스에서 블록 탐색
    if ((bp = find_fit(asize)) != NULL)
    {                     // 적합한 블록 찾음
        place(bp, asize); // 블록 할당
        return bp;
    }

    // 적합한 블록을 찾지 못한 경우, 힙을 확장하고 새로운 블록 할당
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }

    place(bp, asize); // 블록 할당

    return bp;
}

// mm_free - 사용하지 않을 블록을 해제합니다.
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

// mm_realloc - mm_malloc 및 mm_free로 간단하게 구현합니다.
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 새로운 메모리 블록 할당
    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    // 이전 블록의 데이터 크기를 가져옴
    copySize = GET_SIZE(HDRP(oldptr));

    // 실제 복사할 데이터 크기는 이전 블록 크기와 요청된 새 블록 크기 중 작은 값
    if (size < copySize)
        copySize = size;

    // 데이터를 새 블록으로 복사
    memcpy(newptr, oldptr, copySize);

    // 이전 블록 해제
    mm_free(oldptr);

    return newptr;
}

// 요청된 크기에 맞는 가장 적합한 free block을 찾는 함수
// Seglist를 순회하여 적절한 크기의 블록을 찾음
// 사이즈 클래스별로 분리된 리스트에서 적합한 블록을 찾는 함수
static void *find_fit(size_t asize)
{
    void *bp;

    // 요청 인덱스로 크기에 맞는 사이즈 클래스를 찾아 해당 클래스부터 탐색 시작
    for (int classIndex = find_class_index(asize); classIndex < MAX_SIZE_CLASS; classIndex++)
    {
        for (bp = seg_free_list[classIndex]; bp != NULL; bp = GET_NEXT_FREEBLK(bp))
        {
            if (asize <= GET_SIZE(HDRP(bp)))
            {
                return bp; // 적합한 블록을 찾았으면 반환
            }
        }
    }

    return NULL; // 적합한 블록을 찾지 못함
}

// 할당된 블록에 메모리를 할당
// 필요하다면 남은 부분을 분할하여 free list에 추가
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 알아냄

    // 남은 공간이 충분히 클 경우, 즉 요청한 크기(asize)와 현재 크기(csize)의 차이가
    // 두 배의 더블 사이즈(DSIZE)보다 크거나 같으면 블록을 나눔
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));           // 사용할 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(asize, 1));           // 사용할 블록의 푸터에도 똑같이 저장
        bp = NEXT_BLKP(bp);                      // 나머지 블록으로 포인터 이동
        PUT(HDRP(bp), PACK(csize - asize, 0));   // 나머지 블록의 헤더에 크기와 빈 상태 저장
        PUT(FTRP(bp), PACK(csize - asize, 0));   // 나머지 블록의 푸터에도 똑같이 저장
        add_block_to_seglist(bp, csize - asize); // 남은 부분을 적절한 사이즈 클래스에 추가
    }
    else // 남은 공간이 충분히 크지 않으면 현재 블록 전체 사용
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 현재 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(csize, 1)); // 현재 블록의 푸터에도 똑같이 저장
    }
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 확장할 크기를 정렬 요구 사항에 맞게 조정
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    // 새로 확장된 영역의 프리 블록 헤더와 푸터, 그리고 새 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 프리 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 프리 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    // 인접한 프리 블록과의 병합을 시도하여 메모리 단편화 감소
    bp = coalesce(bp);

    // 병합된 가용 블록을 적절한 사이즈 클래스의 segregated free list에 추가
    add_block_to_seglist(bp, size);

    return bp;
}

// 인접한 free block을 병합하는 기존 함수를 seglist 방식에 맞게 조정
// 병합된 블록을 적절한 seglist에 재배치
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    { // 다음 블록만 가용
        remove_block_from_seglist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // 이전 블록만 가용
        remove_block_from_seglist(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc)
    { // 이전과 다음 블록 모두 가용
        remove_block_from_seglist(PREV_BLKP(bp));
        remove_block_from_seglist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // 병합된 블록을 적절한 사이즈 클래스의 리스트에 추가
    add_block_to_seglist(bp, size);
    return bp;
}

// Free block을 적절한 seglist에 삽입하는 함수. Free 또는 Coalesce 과정에서 사용
// 메모리 블록을 적절한 사이즈 클래스의 리스트에 추가하는 함수
static void add_block_to_seglist(void *bp, size_t size)
{
    // 1. 적절한 사이즈 클래스 찾기
    int class_index = find_class_index(size);

    // 2. 현재 블록을 리스트의 첫 번째 위치에 추가
    // 만약 해당 사이즈 클래스에 다른 블록이 이미 있다면, 그 블록을 현재 블록 다음으로 설정
    if (seg_free_list[class_index] != NULL)
    {
        SET_NEXT_FREEBLK(bp, seg_free_list[class_index]);
        SET_PREV_FREEBLK(seg_free_list[class_index], bp);
    }

    // 3. 새로운 블록을 리스트의 시작점으로 설정
    seg_free_list[class_index] = bp;
    SET_PREV_FREEBLK(bp, NULL);
}

// Free list에서 특정 블록을 제거하는 함수. 할당 과정에서 사용
// 메모리 블록을 사이즈 클래스의 리스트에서 제거하는 함수
static void remove_block_from_seglist(void *bp)
{
    int class_index = find_class_index(GET_SIZE(HDRP(bp)));

    // 만약 이 블록이 리스트의 첫 번째 블록이라면
    if (bp == seg_free_list[class_index])
    {
        seg_free_list[class_index] = GET_NEXT_FREEBLK(bp);
    }

    // 이전 블록과 다음 블록을 연결
    if (GET_PREV_FREEBLK(bp) != NULL)
    {
        SET_NEXT_FREEBLK(GET_PREV_FREEBLK(bp), GET_NEXT_FREEBLK(bp));
    }

    if (GET_NEXT_FREEBLK(bp) != NULL)
    {
        SET_PREV_FREEBLK(GET_NEXT_FREEBLK(bp), GET_PREV_FREEBLK(bp));
    }
}

// 주어진 크기에 맞는 사이즈 클래스 인덱스를 찾는 함수
static int find_class_index(size_t size)
{
    for (int i = 0; i < MAX_SIZE_CLASS; i++)
    {
        if (size <= size_classes[i])
        {
            return i; // 주어진 크기가 현재 사이즈 클래스 범위에 들어오면 인덱스 반환
        }
    }

    return MAX_SIZE_CLASS - 1; // 가장 큰 사이즈 클래스 반환
}