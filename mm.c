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

// Basic constants and macros
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define SEGLIMIT 12

// calculate max value
#define MAX(x, y) ((x)>(y) ? (x) : (y))

//size와 할당 여부를 하나로 합친다
#define PACK(size, alloc) ((size)|(alloc))

//포인터 p가 가리키는 주소의 값을 가져온다.
#define GET(p) (*(unsigned int *)(p))

//포인터 p가 가리키는 곳에 val을 역참조로 갱신
#define PUT(p, val) (*(unsigned int *)(p)=(val))

//포인터 p가 가리키는 곳의 값에서 하위 3비트를 제거하여 블럭 사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_SIZE(p) (GET(p) & ~0X7)
//포인터 p가 가리키는 곳의 값에서 맨 아래 비트를 반환하여 할당상태 판별
#define GET_ALLOC(p) (GET(p) & 0X1)

//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//블럭포인터 -> 블럭포인터 - WSIZE : 헤더위치 -> GET_SIZE으로 현재 블럭사이즈계산 -> 다음 블럭포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
//블럭포인터 -> 블럭포인터 - DSIZE : 이전 블럭 푸터 -> GET_SIZE으로 이전 블럭사이즈계산 -> 이전 블럭포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//포인터 p가 가리키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

//segregated list 내에서 next 와 prev의 포인터를 반환
#define PREV_FREE(bp) (*(void **)(bp))
#define NEXT_FREE(bp) (*(void **)(bp + WSIZE))

/* private variables */
/*static char *mem_start_brk;  *//* points to first byte of heap *//*
static char *mem_brk;        *//* points to last byte of heap *//*
static char *mem_max_addr;   *//* largest legal heap address */

//SEG
static char *heap_listp;
#define START(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static int getclass(size_t size);


//함수 목록
static void *coalesce(void *bp);

static void *extend_heap(size_t words);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

static void addfreeblock(void *bp);

static void removefreeblock(void *bp);

int mm_init(void) {
    heap_listp = mem_sbrk((SEGLIMIT + 4) * WSIZE);  // 16 Word + SEG 리스트 만큼 늘리기

    if (heap_listp == (void *) -1)
        return -1;

    PUT(heap_listp, 0);                                                            // Padding 생성
    PUT(heap_listp + (1 * WSIZE), PACK((SEGLIMIT + 2) * WSIZE, 1));                // Prologue header 생성
    for (int i = 0; i < SEGLIMIT; i++) PUT(heap_listp + ((2 + i) * WSIZE), NULL);  // Seg Free List 생성
    PUT(heap_listp + ((SEGLIMIT + 2) * WSIZE), PACK((SEGLIMIT + 2) * WSIZE, 1));   // Prologue Footer 생성
    PUT(heap_listp + ((SEGLIMIT + 3) * WSIZE), PACK(0, 1));                        // Epilogue Header 생성


    heap_listp += DSIZE; //프롤로그 블록을 건너뛰고, 메모리 할당 요청 시 검색을 시작할 적절한 위치로 포인터를 조정

    if (extend_heap(4) == NULL) {
        return -1;
    }

    // 두 가지 다른 경우에 호출된다.
    // (1) 힙이 초기화 될때 (2) mm_malloc이 적당한 맞춤fit을 찾지 못했을 때
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)  // extend_heap을 통해 시작할 때 힙을 한번 늘려줌
        return -1;

    return 0;
}

/*
 * 가용 블록끼리 연결
 */
void addfreeblock(void *bp) {  // Stack형 구조로 만들었기 때문에
    int class = getclass(GET_SIZE(HDRP(bp)));

    NEXT_FREE(bp) = START(class);  // 현재 블록의 NEXT에 기존의 시작 포인터를 삽입
    PREV_FREE(bp) = NULL;
    if (START(class) != NULL)
        PREV_FREE(START(class)) = bp;  // 기존 블록의 PREV를 현재 블록에 연결
    START(class) = bp;                 // class의 시작점이 나를 가리키게 함
}

/*
 * 가용 블록 삭제
 */
void removefreeblock(void *bp) {
    int class = getclass(GET_SIZE(HDRP(bp)));

    if (bp == START(class))            // 첫번째 블록을 삭제 할 경우
        START(class) = NEXT_FREE(bp);  // class의 시작점을 다음 블록으로 연결
    else {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);      // 이전 블록의 NEXT를 다음 블록으로 연결
        if (NEXT_FREE(bp) != NULL)                     // 다음 블록이 있을 경우에
            PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);  // 다음 블록의 PREV를 이전 블록으로 연결
    }
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = words * DSIZE;
    bp = mem_sbrk(size);

    if ((long) bp == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));          // Free Block Header 생성
    PUT(FTRP(bp), PACK(size, 0));          // Free Block Footer 생성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // Epilogue Header 이동

    return coalesce(bp);
}

/*
 * 블록을 연결하는 함수
 */
void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블록의 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 블록의 가용 여부
    size_t size = GET_SIZE(HDRP(bp));                    // 현재 블록의 크기

    // CASE 1: 이전과 다음 블록이 모두 할당되어 있다면 PASS

    if (prev_alloc && !next_alloc) {            // CASE 2: 이전 블록은 할당상태, 다음블록은 가용상태
        removefreeblock(NEXT_BLKP(bp));         // 다음 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 현재 블록을 다음 블록까지 포함한 상태로 변경
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {       // CASE 3: 이전 블록은 가용상태, 다음 블록은 할당상태
        removefreeblock(PREV_BLKP(bp));         // 이전 블록을 가용리스트에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 현재 블록을 이전 블록까지 포함한 상태로 변경
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  // 이전 블록의 헤더 이동
    } else if (!prev_alloc && !next_alloc) {  // CASE 4: 이전과 다음 블록 모두 가용상태다.
        removefreeblock(NEXT_BLKP(bp));     // 이전과 다음 블록을 가용리스트에서 제거
        removefreeblock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // 현재 블록을 이전 블록부터 다음 블록까지 포함한 상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
    }

    addfreeblock(bp);  // 가용 리스트에 블록 추가
    return bp;
}


/*
 * 가용 블록의 Address를 찾는 함수
 *
 */

static void *find_fit(size_t asize) //
{
    int class;
    void *bp;

    // 적절한 크기의 클래스를 찾기 시작합니다. getclass 함수는 주어진 asize에 따라 적절한 클래스를 반환합니다.
    for (class = getclass(asize); class < SEGLIMIT; class++) {
        // 해당 클래스의 리스트를 순회합니다. START 매크로(또는 함수)는 주어진 클래스에 대한 리스트의 시작을 반환합니다.
        for (bp = START(class); bp != NULL; bp = NEXT_FREE(bp)) {
            // 현재 블록의 크기가 요청된 사이즈 이상인지 확인합니다.
            if (GET_SIZE(HDRP(bp)) >= asize) {
                // 적절한 블록을 찾았으면, 해당 블록의 주소를 반환합니다.
                return bp;
            }
        }
    }

    // 적절한 블록을 찾지 못한 경우 NULL을 반환합니다.
    return NULL;
    /*int class;
    void *bp;
    void *best = NULL;

    for (class = getclass(asize); class < SEGLIMIT; class++) {  // 클래스 내에서 찾다가 넣을 수 있는 가용 블록이 없으면 다음 클래스에서 탐색
        for (bp = START(class); bp != NULL; bp = NEXT_FREE(bp))
            if (GET_SIZE(HDRP(bp)) >= asize) {
                if (GET_SIZE(HDRP(bp)) == asize)  // 딱 맞는 사이즈가 있을 경우 더이상 탐색하지 않고 bp 반환
                    return bp;

                best = bp;  // best에 일단 들어갈 수 있는 bp 넣고 다시 탐색 (if문 수행을 줄이기 위해 for문 분할)
                break;
            }

        for (; bp != NULL; bp = NEXT_FREE(bp))
            if (GET_SIZE(HDRP(bp)) >= asize) {
                if (GET_SIZE(HDRP(bp)) == asize)
                    return bp;

                if ((long) (GET_SIZE(HDRP(bp)) < (long) (GET_SIZE(HDRP(best)))))
                    best = bp;
            }
        if (best != NULL)  // class에서 best를 이미 할당했을 경우 다른 class에서 탐색하지 않고 탈출
            break;
    }

    return best;*/
}


/*
 * void bp*: bp 가용 블록의 주소
 * size_t asize: 가용블록에 할당하는 size
 */
// 블록의 포인터(bp)와 할당하려는 크기(asize)를 인자로 받아, 실제 메모리 할당 과정을 수행하는 함수
// 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t diff_size = csize - asize;

    removefreeblock(bp);

    if (diff_size >= (2 * DSIZE)) {
        // printf("block 위치 %p | 들어갈 list의 크기 %d | 넣어야 할 size 크기 %d\n", (int *) bp, GET_SIZE(HDRP(bp)), asize);

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록(분할한)으로 포인터 이동

        //printf("free block 위치 %p | 나머지 block 크기 %d\n", (int *) NEXT_BLKP(bp), diff_size);
        PUT(HDRP(bp), PACK(csize - asize, 0));// 새로 분할된 블록의 헤더,푸터를 남은 크기와 미할당 상태로 설정
        PUT(FTRP(bp), PACK(csize - asize, 0));
        addfreeblock(bp);
        return;
    }
    //printf("block 위치 %p | padding으로 넣은 size 크기 %d\n", (unsigned int *) bp, csize);
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
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

    bp = extend_heap(asize / DSIZE);
    // printf("사이즈 부족으로 Chuncksize %d 연장\n", extendsize);
    if (bp == NULL)
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
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);
    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사
    mm_free(ptr);                  // 기존 블록 해제
    return newptr;
}

int getclass(size_t size) {
    size_t class_size = 16;

    for (int i = 0; i < SEGLIMIT; i++) {
        if (size <= class_size)
            return i;      // 클래스에 해당할 시 클래스 리턴
        class_size <<= 1;  // class size 증가
    }

    return SEGLIMIT - 1;  // size가 65536바이트 초과 시 마지막 클래스로 처리
}


