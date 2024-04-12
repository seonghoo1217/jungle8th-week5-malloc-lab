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

#define MAX(x,y) ((x) > (y) ? (x): (y))

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
int mm_init(void)
{
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
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
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














