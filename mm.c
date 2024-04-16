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
        "3team",
        /* First member's full name */
        "Seong Ho Lee ",
        /* First member's email address */
        "lsh6451217@gmail.com",
        /* Second member's full name (leave blank if none) */
        "Jae Hyeok Jeung",
        /* Second member's email address (leave blank if none) */
        "zaqokm2@gmail.com"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))
/*
 * mm_init - initialize the malloc package.
 */

/* private variables */
/*static char *mem_start_brk;  *//* points to first byte of heap *//*
static char *mem_brk;        *//* points to last byte of heap *//*
static char *mem_max_addr;   *//* largest legal heap address */

static char *last_bp;
static char *heap_listp;
static char *free_listp;

static void *coalesce_with_LIFO(void *bp);

void remove_in_freelist(void *bp);

void put_front_of_freelist(void *bp);

static void *extend_heap(size_t words);

// void *mm_malloc(size_t size);
static void place(void *bp, size_t asize);

static void *find_fit(size_t asize);

/* for explicit*/
#define PREV_FREEP(bp) (*(void **)(bp))
#define NEXT_FREEP(bp) (*(void **)(bp + WSIZE))

int mm_init(void) {
    // mem_sbrk: 힙 영역을 incr(0이 아닌 양수) bytes 만큼 확장하고, 새로 할당된 힙 영역의 첫번째 byte를 가리키는 제네릭 포인터를 리턴함
    /* 비어있는 heap을 만든다.*/
    // (void *)-1의 경우 에러 상황을 나타내는 전통적인 방법 중 하나 , -1이 return되는 케이스
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) -1)
        return -1;

    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE * 2, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), NULL);               /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), NULL);               /* PREV */
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE * 2, 1)); /* NEXT */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */
    heap_listp += (2 * WSIZE); // 포인터를 Prologue Header 뒤로 이동
    free_listp = heap_listp;
//    last_bp = heap_listp;

    if (extend_heap(4) == NULL) {
        return -1;
    }

    // 두 가지 다른 경우에 호출된다.
    // (1) 힙이 초기화 될때 (2) mm_malloc이 적당한 맞춤fit을 찾지 못했을 때
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)  // extend_heap을 통해 시작할 때 힙을 한번 늘려줌
        return -1;

    return 0;
}

static void *extend_heap(size_t words) {
    // 요청한 크기를 인접 2워드의 배수(8바이트)로 반올림하여, 그 후에 추가적인 힙 공간 요청
    char *bp;
    size_t size;
    // 요청한 크기를 2워드의 배수로 반올림하고 추가 힙 공간을 요청함
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;


    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /*coalesce(bp)*/;
    return coalesce_with_LIFO((bp));
};

void remove_in_freelist(void *bp) {
    // Free list의 첫번째 블록 없앨 때, 당연히 prev도 없을듯
    if (bp == free_listp) {
        PREV_FREEP(NEXT_FREEP(bp)) = NULL;
        free_listp = NEXT_FREEP(bp);
    }
        // free list 안에서 없앨 때
    else {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}

void put_front_of_freelist(void *bp) {
    NEXT_FREEP(bp) = free_listp;
    PREV_FREEP(bp) = NULL;
    PREV_FREEP(free_listp) = bp;
    free_listp = bp; // bp가 첫번째 블럭이므로
}

static void *coalesce_with_LIFO(void *ptr) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) { /* Case 1: 앞뒤로 꽉~ 막혀있을 때 */
        last_bp = ptr;
    } else if (prev_alloc && !next_alloc) { /* Case 2: 뒤는 막혀있고, 앞(다음)은 비어있을 때 */
        remove_in_freelist(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) { /* Case 3: 뒤는 비어있고, 앞(다음)은 막혀있을 때 */
        remove_in_freelist(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else { /* Case 4: 앞뒤 모두 비어있을 때*/
        remove_in_freelist(PREV_BLKP(ptr));
        remove_in_freelist(NEXT_BLKP(ptr));

        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
                GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);

    }
//    last_bp = ptr;
    put_front_of_freelist(ptr);
    return ptr;
}

/*
 * 가용 블록의 Address를 찾는 함수
 *
 */

static void *find_fit(size_t asize) //
{
    for (void *bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT_FREEP(bp)) // TBD (next찾아다니면서 )프리 리스트로 바꾸기
    {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
    /*void *best_bp = NULL; // 최적의 블록 포인터 초기화
    size_t min_diff = (size_t)-1; // 최소 크기 차이를 최대로 설정하여 초기화

    void *bp;
    // free_listp부터 시작하여 가용 블록 리스트를 순회
    for (bp = free_listp; bp != NULL; bp = NEXT_BLKP(bp)) {

        size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기
        // 현재 블록이 요청 사이즈보다 크거나 같고, 현재까지 찾은 최소 차이보다 작은 경우
        if ((csize >= asize) && ((csize - asize) < min_diff)) {
            printf("!!");
            best_bp = bp; // 최적의 블록 업데이트
            min_diff = csize - asize; // 최소 차이 업데이트

            if (min_diff == 0) {
                // 완벽하게 맞는 블록을 찾은 경우, 더 이상 탐색 중단
                break;
            }
        }

    }

    return best_bp;*/
}


/*
 * void bp*: bp 가용 블록의 주소
 * size_t asize: 가용블록에 할당하는 size
 */
// 블록의 포인터(bp)와 할당하려는 크기(asize)를 인자로 받아, 실제 메모리 할당 과정을 수행하는 함수
// 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_in_freelist(bp);
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록(분할한)으로 포인터 이동
        PUT(HDRP(bp), PACK(csize - asize, 0));// 새로 분할된 블록의 헤더,푸터를 남은 크기와 미할당 상태로 설정
        PUT(FTRP(bp), PACK(csize - asize, 0));
        put_front_of_freelist(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

//size만큼 메모리를 할당함
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    // size를 바탕으로 헤더와 푸터의 공간 확보
    // 8바이트는 정렬조건을 만족하기 위해
    // 추가 8바이트는 헤더와 푸터 오버헤드를 위해서 확보
    if (size <= DSIZE) {
        /*
         * 만약 요청된 메모리의 크기(size)가 DSIZE보다 작거나 같다면, 할당할 메모리의 크기(asize)는 2*DSIZE로 설정됩니다.
         * 여기서 DSIZE는 '더블 워드 크기'를 의미하며, 시스템의 최소 메모리 할당 단위
         */
        asize = 2 * DSIZE;
    } else {
        /*
         * 요청된 크기가 DSIZE의 배수가 되도록 합니다.
         * 이를 위해 (size + (DSIZE) + (DSIZE - 1))를 계산한 후, 이를 DSIZE로 나누어 올림 처리합니다.
         * 여기서 (DSIZE - 1)을 더하는 것은 올림을 구현하기 위한 것입니다.
         * 예를 들어, size가 DSIZE의 배수가 아닌 경우, 나눗셈의 결과가 정수가 아니게 됩니다. 이때 (DSIZE - 1)을 더하면, DSIZE로 나누었을 때 올림이 발생하게 됩니다.
         */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    //first_fit으로 NULL이 아닌 메모리 공간을 찾으면 할당
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
//        last_bp = bp;
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    last_bp = bp;
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));

    // 헤더와 푸터를 0으로 할당하고 coalesce를 호출하여 가용 메모리를 이어준다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce_with_LIFO(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL)  // pointer가 비어 있으면 malloc 함수와 동일하게 동작
        return mm_malloc(size);

    if (size <= 0) {  // memory size가 0이면 메모리 free
        mm_free(ptr);
        return NULL;
    }

    void *newp = mm_malloc(size);
    // newp가 가리키는 주소가 NULL(할당되었다고 생각했지만 실패한 경우)
    if (newp == NULL) {
        return 0;
    }
    // 진짜 realloc 하는 코드임.
    size_t oldsize = GET_SIZE(HDRP(ptr));
    // ex int a(oldsize) = 10(GET_SIZE(HDRP(ptr));)
    // 그러므로 일단 여기까진 a = 10
    // 재할당이라는 것은 get_size 한 10값을 a(기존데이터주소)가 아닌 b(다른데이터주소)
    // 에 넣는다는 것이다.
    /*
    새로 할당하고자 하는 크기가 oldsize 보다 작으면
    그런데 oldsize가 가진 데이터의 크기가 size의 데이터 크기보다 크기때문에
    커서 전부 다 못들어간다. 그러면은 일단 size 만큼의 데이터만 size에 재할당하고
    나머지 부분(데이터)는 버린다. (가비지데이터)
    */
    if (size < oldsize) {
        oldsize = size; // oldsize의 데이터크기를 size 크기만큼 줄이겠다는 뜻.
    }

    // oldsize 데이터를  ptr(기존 주소) 에서 newp(새로 할당될 주소) 로 옮겨준다.
    memcpy(newp, ptr, oldsize);
    mm_free(ptr); // 원래 기존 주소에 있던 데이터를 free 시킨다.
    return newp;
}














