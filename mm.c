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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// ----- KJ -----

/* 가용리스트 조작 매크로*/
#define WSIZE 4             /* 워드 크기 */
#define DSIZE 8             /* 더블워드 크기 */
#define CHUNKSIZE (1 << 12) /* 2의 12승 비트연산 (4096) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* 인자 p가 참조하는 워드를 읽어서 리턴, 인자 p가 가르키는 워드에 val을 저장*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 헤더 또는 풋터의 size와 리턴한다. p의 메모리 블록의 크기를 추출하기위해 사용,
 주소 p에 있는 헤더 또는 풋터의 할당비트를 리턴한다. p의 메모리블록 할당여부를 확인하기위해 사용*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)


/* 블록 헤더를 가리키는 포인터를 리턴 -> 데이터의 시작주소에서 헤더의 크기인 4바이트를 빼서 헤더의 시작주소를 나타냄
블록 풋터를 가리키는 포인터를 리턴 -> 데이터의 시작주소에서 헤더에 저장된 크기를 더해서 8바이트를 뺴서 푸터의 시작주소를 나타냄
헤더의 시작주소가 아닌 데이터의 시작주소 부터 시작해서 8바이트를 뺸다.*/
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음 블록의 페이로드 시작 포인터를 리턴
이전 블록의 페이로드 시작 포인터를 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// ----- ** -----
static void *coalesce(void *bp); // 인접하는 가용 블록들을 병합하고 단일 블록으로 만듦
static void *extend_heap(size_t words); // 힙을 확장
static void *heap_listp; // 가용리스트의 시작을 나타내는 포인터
int mm_init(void); // 메모리 시스템 초기화, 초기 빈 가용리스트 생성
void *mm_malloc(size_t size); // 요청된 크기의 메모리 블록을 할당
void mm_free(void *ptr); // 이전에 할당된 메모리 블록을 해제, 블록을 가용 리스트에 추가
void *mm_realloc(void *ptr, size_t size); // 이전에 할당된 메모리 블록의 크기를 조정하거나 새로운 위치로 메모리 이동
static void *find_fit(size_t asize); // 요청된 크기에 맞는 가용 블록 탐색
static void *find_nextp; // 다음 가용 블록을 탐색하기 위한 포인터
static void *next_fit(size_t asize); // 다음 가용 블록을 찾을 때 현재 위치를 기준으로 탐색
static void place(void *bp, size_t aszie); // 할당된 메모리 블록을 가용 리스트에서 제거하고 요청된 크기로 분할
// ----- KJ -----

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) /* Case 1 */
    {
        return bp;
    }

    if (prev_alloc && !next_alloc) /* Case 2 */
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) /* Case 3 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else /* Case 4 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

// ----- ** -----

// ----- KJ -----

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

// ----- ** -----

/*
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    /* Create the initial empty heap */
    //mem_sbrk 는 리눅스 시스템에서 sbrk로 대체할 수 있다. mem_sbrk는 다양한 운영체제에서 사용한다.
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) //초기 메모리 블록을 요청하고 그결과를 heap_listp에 할당한다.
        return -1; // 할당에 실패하면 (void *)-1를 반환하는데 반환값과 (void *)-1를 비교해서 할당실패이면 -1을 반환한다.

    PUT(heap_listp, 0);                            
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); //헤더로 구성된 8바이트 블록
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); //푸터로 구성된 8바이트 블록
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     //에필로그 블록 크기가 0
    heap_listp += (2 * WSIZE);                     //프롤로그 블록과 에필로그 블록 사이 힙의 시작 주소를 나타냄
    find_nextp = heap_listp; // next_fit을 사용할 떄 필요한 변수
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
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
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);

    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

//

// ----- KJ -----

// void *mm_malloc(size_t size)
// {
//     size_t asize;      /* Adjusted block size */
//     size_t extendsize; /* Amount to extend heap if no fit */
//     char *bp;

//     /* Ignore spurious requests */
//     if (size == 0)
//         return NULL;

//     /* Adjust block size to include overhead and alignment reqs. */
//     if (size <= DSIZE)
//         asize = 2 * DSIZE;
//     else
//         asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

//     /* Search the free list for a fit */
//     // if ((bp = find_fit(asize)) != NULL)
//     // {
//     //     place(bp, asize);
//     //     return bp;
//     // }

//     /* No fit found. Get more memory and place the block */
//     extendsize = MAX(asize, CHUNKSIZE);

//     if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
//         return NULL;

//     // place(bp, asize);
//     return bp;
// }

// ----- ** -----

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;

    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);

    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}
