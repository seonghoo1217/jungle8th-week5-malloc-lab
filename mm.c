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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 가용 리스트 단위를 조작하기 위한 상수 값과 매크로 설정*/
#define WSIZE 4  // word size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // 초기 가용 블록 & 힙 확장을 위한 기본 Chunk size (4kb = 2**12)

#define MAX(x, y) ((x) > (y) ? (x): (y))

/* 헤더와 푸터에 저장할 수 있는 값 리턴*/
#define PACK(size, alloc) ((size) | (alloc)) // size 와 alloc을 합쳐서 block address 제작

/* 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 리턴*/
#define GET(p)      (*(unsigned int *)(p)) // 인자 p에 들어있는 block address 획득
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 인자 p에 다음 block address 할당

/* 주소 p의 헤더 또는 푸터의 SIZE와 할당 비트를 리턴한다.*/
#define GET_SIZE(p)   (GET(p) & ~0x7) // 뒤에 3비트를 제외하고 읽어옴, address에 있는 size 획득 (& 11111000)
#define GET_ALLOC(p)  (GET(p) & 0x1) // 할당 가용 확인 , // address에 있는 alloc 획득 (& 00000001)

/* 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.*/
#define HDRP(bp)    ((char *)(bp) - WSIZE) // Header는 block pointer의 Word Size만큼 앞에 위치
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp))- DSIZE) // Footer는 헤더의 끝 지점부터 block의 사이즈 만큼 더하고 2*word만큼 앞에 위치

/* 다음과 이전 블록 포인터를 각각 리턴한다. 다음 또는 이전 헤더의 위치이기도함*/
#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))) // 다음 block pointer 위치로 이동
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))) // 이전 block pointer 위치로 이동
/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;

/* private variables */
static char *mem_start_brk;  /* points to first byte of heap */
static char *mem_brk;        /* points to last byte of heap */
static char *mem_max_addr;   /* largest legal heap address */
static void *extend_heap(size_t words);

static void *coalesce(void *bp);

int mm_init(void) {
    // mem_sbrk: 힙 영역을 incr(0이 아닌 양수) bytes 만큼 확장하고, 새로 할당된 힙 영역의 첫번째 byte를 가리키는 제네릭 포인터를 리턴함
    /* 비어있는 heap을 만든다.*/
    // (void *)-1의 경우 에러 상황을 나타내는 전통적인 방법 중 하나 , -1이 return되는 케이스
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;

    PUT(heap_listp, 0); // alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // epliogue header
    heap_listp += (2 * WSIZE); // 포인터를 Prologue Header 뒤로 이동

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
    return coalesce(bp);
};

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {              // Case 1 : 이전 ,현재 블록이 모두 할당된 상태
        heap_listp = bp;
        return bp;                              // // 할당이 해제되는 경우밖에 없으므로 이미 현재블록은 가용하므로 리턴
    } else if (prev_alloc && !next_alloc) {         // Case 2 : 이전 블록은 할당상태, 다음블록은 가용상태
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 현재 블록에 다음블록 포함
        PUT(HDRP(bp), PACK(size, 0));           // 헤더 푸터 셋팅
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {         // Case 3 : 이전 블록은 가용, 다음 블록 할당상
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 현재 블록을 이전 블록까지 포함한 상태로 변경
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);// 이전 블록의 헤더 이동
    } else {                                       // Case 4 : 이전 블록과 다음 블록 병합 즉, 모두 가용상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        //bp = PREV_BLKP(bp);             동일하게 동작함
        //PUT(HDRP((bp)), PACK(size, 0));
        //PUT(FTRP(bp), PACK(size, 0));
    }
    heap_listp = bp;
    return bp;
}

/*
 * 가용 블록의 Address를 찾는 함수
 *
 */


static void *find_fit(size_t asize) {
    // 적절한 가용 블록을 검색한다.
    //first fit 검색을 수행한다. -> 리스트 처음부터 탐색하여 가용블록 찾기
    // 무조건 사용만 가능하면되기에 탐색은 빠르지만, 최적의 메모리 사용은 아닐 확률이 있다.
    // next fit, best fit,good fit은 별도 구현
    void *bp;
    //헤더의 사이즈가 0보다 크다. -> 에필로그까지 탐색한다.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

static void *best_fit(size_t asize) {
    void *best_fit = NULL; // 가장 잘 맞는 블록을 저장할 포인터
    size_t smallest_diff = (size_t) - 1; // 가장 작은 크기 차이; 초기값은 최대값으로 설정

    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        size_t csize = GET_SIZE(HDRP(bp));

        if (!GET_ALLOC(HDRP(bp)) && (asize <= csize)) {
            size_t diff = csize - asize; // 현재 블록과 요청 크기의 차이 계산

            // 차이가 0이면, 완벽하게 맞는 블록을 찾은 것이므로 바로 반환
            if (diff == 0) {
                return bp;
            } else if (diff < smallest_diff) { // 더 작은 차이를 가진 블록을 찾으면 업데이트
                best_fit = bp;
                smallest_diff = diff;
            }
        }
    }

    // 가장 잘 맞는 블록 반환 (없으면 NULL)
    return best_fit;
}

//static char *last_bp = NULL;

/*static void *next_fit(size_t asize) {
    // last_bp가 NULL이면, 처음부터 탐색을 시작합니다.
    if (last_bp == NULL) {
        last_bp = heap_listp;
    }
    char *bp = last_bp;

    do {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            // 적절한 크기의 블록을 찾으면 last_bp를 업데이트하고 반환합니다.
            last_bp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
        // 리스트의 끝에 도달하면 처음부터 다시 시작합니다.
        if (GET_SIZE(HDRP(bp)) == 0) {
            bp = heap_listp;
        }
        // last_bp에 도달할 때까지 또는 적절한 블록을 찾을 때까지 반복합니다.
    } while (bp != last_bp);

    return NULL;
}*/
/*
 * void bp*: bp 가용 블록의 주소
 * size_t asize: 가용블록에 할당하는 size
 */
// 블록의 포인터(bp)와 할당하려는 크기(asize)를 인자로 받아, 실제 메모리 할당 과정을 수행하는 함수
// 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록(분할한)으로 포인터 이동
        PUT(HDRP(bp), PACK(csize - asize, 0));// 새로 분할된 블록의 헤더,푸터를 남은 크기와 미할당 상태로 설정
        PUT(FTRP(bp), PACK(csize - asize, 0));
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
    /*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/
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
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
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
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    /*void *oldptr = ptr;
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
    return newptr;*/
    if (ptr == NULL)  // pointer가 비어 있으면 malloc 함수와 동일하게 동작
        return mm_malloc(size);

    if (size <= 0) {  // memory size가 0이면 메모리 free
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    copySize = GET_SIZE(HDRP(ptr));

    if (size < copySize)  // 현재 memory보다 크면 memory를 늘려서 새로 할당
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














