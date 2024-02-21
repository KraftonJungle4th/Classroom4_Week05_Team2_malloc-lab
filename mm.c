#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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
    printf("[mm_init] 함수 시작\n");

    // 1. seg_free_list 초기화
    for (int i = 0; i < MAX_SIZE_CLASS; i++)
    {
        seg_free_list[i] = NULL;
    }

    // 2. 초기 힙 영역 설정
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        printf("[mm_init] 함수 종료, ERROR: (heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1\n");

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
        printf("[mm_init] 함수 종료, ERROR: extend_heap(CHUNKSIZE / WSIZE) == NULL\n");

        return -1;
    }

    printf("[mm_init] 함수 종료\n");

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
// 메모리 블록을 할당하는 함수, size는 payload의 크기
void *mm_malloc(size_t size)
{
    printf("[mm_malloc] 함수 시작, size: %zu\n", size);

    size_t asize;      // 조정된 블록 크기
    size_t extendsize; // 필요한 경우 힙을 확장할 크기
    char *bp;

    // 요청된 크기가 0이면 할당하지 않음
    if (size == 0)
    {
        printf("[mm_malloc] 함수 종료, ERROR: size == 0\n");

        return NULL;
    }

    // 블록 크기를 조정 (예: 헤더와 푸터 크기 포함)
    asize = size <= DSIZE
                ? 2 * DSIZE
                : DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 적절한 사이즈 클래스에서 블록 탐색
    if ((bp = find_fit(asize)) != NULL)
    {                                                                            // 적합한 블록 찾음
        place(bp, asize);                                                        // 블록 할당
        printf("[mm_malloc] 함수 종료, 할당된 블록 %p, 크기: %zu\n", bp, asize); // 디버깅 로그 추가

        return bp;
    }

    // 적합한 블록을 찾지 못한 경우, 힙을 확장하고 새로운 블록 할당
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }

    place(bp, asize); // 블록 할당

    printf("[mm_malloc] 함수 종료, size: %zu\n", size);

    return bp;
}

// mm_free - 사용하지 않을 블록을 해제합니다.
void mm_free(void *ptr)
{
    printf("[mm_free] 함수 시작, ptr: %p\n", ptr);

    size_t size = GET_SIZE(HDRP(ptr));

    printf("[mm_free] 해제되는 블록 %p, 크기: %zu\n", ptr, size); // 디버깅 로그 추가

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);

    printf("[mm_free] 함수 종료, ptr: %p\n", ptr);
}

// mm_realloc - mm_malloc 및 mm_free로 간단하게 구현합니다.
void *mm_realloc(void *ptr, size_t size)
{
    printf("[mm_realloc] 함수 시작, ptr: %p, size: %zu\n", ptr, size);

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 새로운 메모리 블록 할당
    newptr = mm_malloc(size);

    if (newptr == NULL)
    {
        printf("[mm_realloc] 함수 종료, newptr == NULL");
        return NULL;
    }

    // 이전 블록의 데이터 크기를 가져옴
    copySize = GET_SIZE(HDRP(oldptr));

    // 실제 복사할 데이터 크기는 이전 블록 크기와 요청된 새 블록 크기 중 작은 값
    if (size < copySize)
    {
        copySize = size;
    }

    // 데이터를 새 블록으로 복사
    memcpy(newptr, oldptr, copySize);

    // 이전 블록 해제
    mm_free(oldptr);

    printf("[mm_realloc] 함수 종료, ptr: %p, size: %zu\n", ptr, size);

    return newptr;
}

// 요청된 크기에 맞는 가장 적합한 free block을 찾는 함수
// Seglist를 순회하여 적절한 크기의 블록을 찾음
// 사이즈 클래스별로 분리된 리스트에서 적합한 블록을 찾는 함수
static void *find_fit(size_t asize)
{
    printf("[find_fit] 함수 시작, 요청 크기(asize): %zu\n", asize);

    // 요청 인덱스로 크기에 맞는 사이즈 클래스를 찾아 해당 클래스부터 탐색 시작
    for (int classIndex = find_class_index(asize); classIndex < MAX_SIZE_CLASS; classIndex++)
    {
        printf("[find_fit] 사이즈 클래스 %d 검색 중...\n", classIndex);

        for (void *bp = seg_free_list[classIndex]; bp != NULL; bp = GET_NEXT_FREEBLK(bp))
        {
            // 메모리 접근 전 유효 범위 검사
            if (bp == NULL || bp < mem_heap_lo() || bp > mem_heap_hi())
            {
                printf("[find_fit] Error: 메모리 접근 범위를 벗어남 %p\n", bp);
                break; // 또는 다른 오류 처리
            }

            if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
            {
#ifdef DEBUG
                printf("[find_fit] 적합한 블록 찾음 %p, 크기: %zu\n", bp, GET_SIZE(HDRP(bp)));

                printf("[find_fit] GET(%p): %u\n", bp, GET(bp));
                printf("[find_fit] GET_SIZE(%p): %zu\n", bp, GET_SIZE(HDRP(bp)));
                printf("[find_fit] GET_ALLOC(%p): %d\n", bp, GET_ALLOC(HDRP(bp)));

                printf("[find_fit] 함수 종료, 요청 크기(asize): %zu\n", asize);
#endif

                return bp; // 적합한 블록을 찾았으면 반환
            }
        }
    }

#ifdef DEBUG
    printf("[find_fit] ERROR: 적합한 블록 찾지 못함\n");
#endif
    return NULL; // 적합한 블록을 찾지 못함
}

// 할당된 블록에 메모리를 할당
// 필요하다면 남은 부분을 분할하여 free list에 추가
static void place(void *bp, size_t asize)
{
    printf("[place] 함수 시작, bp: %p, asize: %zu\n", bp, asize);

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 알아냄

    printf("[place] 블록 할당 시작 %p, 요청 크기: %zu, 현재 블록 크기: %zu\n", bp, asize, csize);

    // 남은 공간이 충분히 클 경우, 즉 요청한 크기(asize)와 현재 크기(csize)의 차이가
    // 두 배의 더블 사이즈(DSIZE)보다 크거나 같으면 블록을 나눔
    if ((csize - asize) >= (2 * DSIZE))
    {
        printf("[place] 블록 분할 발생, 할당 크기: %zu, 남은 크기: %zu\n", asize, csize - asize);

        // 분할 로직
        PUT(HDRP(bp), PACK(asize, 1));           // 사용할 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(asize, 1));           // 사용할 블록의 푸터에도 똑같이 저장
        bp = NEXT_BLKP(bp);                      // 나머지 블록으로 포인터 이동
        PUT(HDRP(bp), PACK(csize - asize, 0));   // 나머지 블록의 헤더에 크기와 빈 상태 저장
        PUT(FTRP(bp), PACK(csize - asize, 0));   // 나머지 블록의 푸터에도 똑같이 저장
        add_block_to_seglist(bp, csize - asize); // 남은 부분을 적절한 사이즈 클래스에 추가
    }
    else // 남은 공간이 충분히 크지 않으면 현재 블록 전체 사용
    {
        // 전체 블록 사용
        printf("[place] 전체 블록 사용 %p, 크기: %zu\n", bp, csize);

        PUT(HDRP(bp), PACK(csize, 1)); // 현재 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(csize, 1)); // 현재 블록의 푸터에도 똑같이 저장

        // 현재 블록을 free list에서 제거
        remove_block_from_seglist(bp);
    }

    printf("[place] Block %p - size: %zu, allocated: %d\n", bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));

    printf("[place] 함수 종료, bp: %p, asize: %zu\n", bp, asize);
}

static void *extend_heap(size_t words)
{
    printf("[extend_heap] 함수 시작, words: %zu\n", words);

    char *bp;

    // 확장할 크기를 정렬 요구 사항에 맞게 조정
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    printf("[extend_heap] 힙 확장 시작, 요청 워드: %zu, 확장 크기: %zu\n", words, size);

    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        printf("[extend_heap] 함수 종료, 힙 확장 실패\n");
        return NULL;
    }

    // 새로 확장된 영역의 프리 블록 헤더와 푸터, 그리고 새 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 프리 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 프리 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    if (bp < (char *)mem_heap_lo() || bp > (char *)mem_heap_hi())
    {
        printf("[extend_heap] 함수 종료, Error: Block %p is outside heap bounds\n", bp);
    }

    printf("[extend_heap] 힙 확장 성공, 새 가용 블록 %p, 크기: %zu\n", bp, size);

    printf("[extend_heap] 함수 종료, words: %zu\n", words);

    // 외부 파편화 때문에 사용
    return coalesce(bp);
}

// 인접한 free block을 병합하는 기존 함수를 seglist 방식에 맞게 조정
// 병합된 블록을 적절한 seglist에 재배치
static void *coalesce(void *bp)
{
    printf("[coalesce] 함수 시작, 적합한 블록 찾지 못함 - bp: %p\n", bp);

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    for (void *segPtr = seg_free_list; segPtr != NULL; segPtr = GET_NEXT_FREEBLK(segPtr))
    {
        printf("[coalesce] Before: Free block %p, next: %p\n", segPtr, GET_NEXT_FREEBLK(segPtr));
    }

    if (prev_alloc && !next_alloc) // 다음 블록만 가용
    {
        printf("[coalesce] 다음 블록이 가용일 때\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block_from_seglist(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 가용
    {
        printf("[coalesce] 이전 블록이 가용일 때\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_block_from_seglist(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc) // 이전과 다음 블록 모두 가용
    {
        printf("[coalesce] 이전과 다음 블록이 가용일 때\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_block_from_seglist(PREV_BLKP(bp));
        remove_block_from_seglist(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    printf("[coalesce] 병합된 블록 %p, 새로운 크기: %zu\n", bp, size); // 디버깅 로그 추가

    // 병합된 블록을 적절한 사이즈 클래스의 리스트에 추가하지만,
    // 중복을 체크하는 로직은 add_block_to_seglist 함수 내부에서 처리.
    // 따라서, 여기서는 별도의 중복 체크 로직을 추가하지 않음
    for (void *segPtr = seg_free_list; segPtr != NULL; segPtr = GET_NEXT_FREEBLK(segPtr))
    {
        printf("[coalesce] After: Free block %p, next: %p\n", segPtr, GET_NEXT_FREEBLK(segPtr));
    }

    add_block_to_seglist(bp, size);

    printf("[coalesce] 함수 종료, bp: %p\n", bp);

    return bp;
}

static void verify_list_integrity(void *head)
{
    printf("[verify_list_integrity] 함수 시작, head: %p\n", head);

    void *slow = head;
    void *fast = head;

    // 리스트 순환 검사 (Floyd의 사이클 찾기 알고리즘)
    while (slow && GET_NEXT_FREEBLK(slow) && fast && GET_NEXT_FREEBLK(fast) && GET_NEXT_FREEBLK(GET_NEXT_FREEBLK(fast)))
    {
        slow = GET_NEXT_FREEBLK(slow);
        fast = GET_NEXT_FREEBLK(GET_NEXT_FREEBLK(fast));

        printf("[verify_list_integrity] slow : %p, fast: %p\n", slow, fast);

        if (slow == fast)
        {
            printf("[verify_list_integrity] 함수 종료, ERROR: 순환 참조가 감지되었습니다.\n");
            return;
        }
    }

    // 연결 무결성 검사
    void *prev = NULL;

    for (void *curr = head; curr != NULL; curr = GET_NEXT_FREEBLK(curr))
    {
        if (GET_PREV_FREEBLK(curr) != prev)
        {
            printf("[verify_list_integrity] 함수 종료, ERROR: 리스트 연결 무결성 오류가 감지되었습니다. 현재 블록: %p, 이전 블록: %p\n", curr, prev);
            return;
        }

        prev = curr;
    }

    printf("[verify_list_integrity] 함수 종료, head: %p\n", head);
}

// Free block을 적절한 seglist에 삽입하는 함수. Free 또는 Coalesce 과정에서 사용
// 메모리 블록을 적절한 사이즈 클래스의 리스트에 추가하는 함수
static void add_block_to_seglist(void *bp, size_t size)
{
    printf("[add_block_to_seglist] 함수 시작, bp: %p, size: %zu\n", bp, size); // 디버깅 로그 추가

    // 1. 적절한 사이즈 클래스 찾기
    int class_index = find_class_index(size);

    // 중복 추가 검증 로직
    for (void *search_bp = seg_free_list[class_index]; search_bp != NULL; search_bp = GET_NEXT_FREEBLK(search_bp))
    {
        if (search_bp == bp)
        {
            printf("[add_block_to_seglist] 함수 종료, Error: 블록 %p는 이미 사이즈 클래스 %d에 추가되어 있습니다.\n", bp, class_index);

            return; // 이 경우 추가 작업을 중단
        }
    }

    // 리스트 무결성 검증 로직 호출
    verify_list_integrity(seg_free_list[class_index]);

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

    printf("[add_block_to_seglist] 추가된 블록 %p, 크기: %zu, 사이즈 클래스: %d\n", bp, size, class_index); // 디버깅 로그 추가

    printf("[add_block_to_seglist] 함수 종료, bp: %p, size: %zu\n", bp, size); // 디버깅 로그 추가
}

// Free list에서 특정 블록을 제거하는 함수. 할당 과정에서 사용
// 메모리 블록을 사이즈 클래스의 리스트에서 제거하는 함수
static void remove_block_from_seglist(void *bp)
{
    printf("[remove_block_from_seglist] 함수 시작, bp: %p\n", bp); // 디버깅 로그 추가

    int class_index = find_class_index(GET_SIZE(HDRP(bp)));
    int found = 0; // 블록이 리스트에 있는지 여부를 추적

    // 리스트에 블록이 실제로 존재하는지 검증
    for (void *search_bp = seg_free_list[class_index]; search_bp != NULL; search_bp = GET_NEXT_FREEBLK(search_bp))
    {
        if (search_bp == bp)
        {
            found = 1;
            break;
        }
    }

    if (!found)
    {
        printf("[remove_block_from_seglist] 함수 종료, Error: 제거하려는 블록 %p가 사이즈 클래스 %d 리스트에 존재하지 않습니다.\n", bp, class_index);
        return; // 이 경우 제거 작업을 중단
    }

#ifdef DEBUG
    // 리스트 무결성 검증 로직 호출
    verify_list_integrity(seg_free_list[class_index]);
#endif

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

    printf("[remove_block_from_seglist] 제거된 블록 %p\n", bp); // 디버깅 로그 추가

    printf("[remove_block_from_seglist] 함수 종료, bp: %p\n", bp); // 디버깅 로그 추가
}

// 주어진 크기에 맞는 사이즈 클래스 인덱스를 찾는 함수
static int find_class_index(size_t size)
{
    printf("[find_class_index] 함수 시작, size: %zu\n", size); // 디버깅 로그 추가

    for (int i = 0; i < MAX_SIZE_CLASS; i++)
    {
        if (size <= size_classes[i])
        {
            printf("[find_class_index] 함수 종료, index: %d\n", i); // 디버깅 로그 추가
            return i;                                               // 주어진 크기가 현재 사이즈 클래스 범위에 들어오면 인덱스 반환
        }
    }

    printf("[find_class_index] 함수 종료, MAX_SIZE_CLASS - 1: %d\n", MAX_SIZE_CLASS - 1); // 디버깅 로그 추가

    return MAX_SIZE_CLASS - 1; // 가장 큰 사이즈 클래스 반환
}