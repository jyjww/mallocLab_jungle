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

/*Basic Constraints and macros*/
#define WSIZE   4
#define DSIZE   8
#define CHUNKSIZE (1<<12)

#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)   ((size) | (alloc))

/*Read and write a word at address p*/
// why uint -> 최상위 비트가 1일때 int는 음수로 읽기 때문에 숫자 그대로 가져오기 위함
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p*/
// read bits and ignore last 3 bits (0x7)
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)  // 할당 여부를 마지막 1비트만 본다

/*Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous block*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*Declaration for static helper functions*/
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *best_fit(size_t asize);
static void *next_fit(void *start_bp, size_t asize);

/*Global pointer to first block*/
static char *heap_listp = NULL;
static int realloc_counter = 0;

/*Static functions*/

static void *extend_heap(size_t words)
{
    /*
    Allocate new memory using mem_sbrk,
    initialize free block & update heap_listp
    */

    char *bp;
    size_t size;

    /*Allocate even number of words to maintain alignment*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /*Initialize free block header/footer and eplilogue header*/
    PUT(HDRP(bp), PACK(size, 0));           //free block header
    PUT(FTRP(bp), PACK(size, 0));           //free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   //new epilogue header

    /*Coalesce if previous block was free*/
    return coalesce(bp);

}

static void *find_fit(size_t asize)
{
    /*First-fit search*/
    void *bp;

    /*Search from head of heap to the end, if not alloc & block bigger or equal to req size, return*/
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;    // No fit
}

static void *best_fit(size_t asize)
{
    /*Best-fit search*/
    void *bp;
    void *best_bp = NULL;
    size_t best_size = (size_t)-1;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            size_t diff = GET_SIZE(HDRP(bp)) - asize;
            /*if smaller diff than prev best_size, save size and bp*/
            if (diff < best_size){
                best_size = diff;
                best_bp = bp;
            }
        }
    }
    /*Search all heap and return best_bp*/
    return best_bp;
}

static void *next_fit(void *start_bp, size_t asize)
{
    /*Next-fit search*/
    void *bp = start_bp;

    /*Search from last_fitp to end*/
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }

    /*Search from start to last_fitp*/
    for (bp = heap_listp; bp != start_bp; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}


static void place(void *bp, size_t asize)
{
    // current block size
    size_t csize = GET_SIZE(HDRP(bp)); 

    if ((csize - asize) >= (2*DSIZE)){
        /*Split block : allocate front part*/
        PUT(HDRP(bp), PACK(asize, 1));      // Set header as allocated(1)
        PUT(FTRP(bp), PACK(asize, 1));      // Set footer as allocated(1)
        
        /*Create new free block with remaining space*/
        bp = NEXT_BLKP(bp);                         // Move to next block
        PUT(HDRP(bp), PACK(csize - asize, 0));      // Set header as free
        PUT(FTRP(bp), PACK(csize - asize, 0));      // Set footer as free
    }
    else{
        /*Do not split : allocate entire block*/
        PUT(HDRP(bp), PACK(csize, 1));          // Set entire block header as allocated
        PUT(FTRP(bp), PACK(csize, 1));          // Set entire block footer as allocated
    }
}

/*mm_init - initialize the malloc package.*/
int mm_init(void)
{
    /*Create the initial empty heap*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);         // alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));     // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));     // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(DSIZE, 1));     //Eplilogue header
    heap_listp += (2*WSIZE);

    //last_fitp = heap_listp;     // Use when next-fit

    /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;           // actual size for allocation
    size_t extendsize;      // amount to extend heap if no fit
    char *bp;               // bp pointer

    /*Ignore req for zero bytes*/
    if (size == 0)
        return NULL;

    /*Adjust block size to include overhead and alignment req*/
    // block is at least 8 bytes(DSIZE)
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /*Search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /*No fit found. Get more memory and place block*/
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}
/*
 * mm_realloc - adaptive realloc
*/
void *mm_realloc(void *bp, size_t size)
{
    realloc_counter++;
    size_t oldsize = GET_SIZE(HDRP(bp));
    size_t newsize;    // define adjusted

    /*Adjust req size to meet overhead, alignment*/
    if (size <= DSIZE)
        newsize = 2 * DSIZE;
    else
        newsize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* If cur block is enough, return */
    if (newsize <= oldsize) {
        return bp;
    }

    /*Adaptive: early stage -> malloc+memcpy, later -> try merging*/
    if (realloc_counter < 50){
        /*Early stage : always allocate new*/
        void *new_bp = mm_malloc(newsize);
        if (new_bp == NULL) return NULL;
        memcpy(new_bp, bp, oldsize);
        mm_free(bp);
        return new_bp;
    }
    else{
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

        /*If next block is free and can merge to newsize*/
        if (!next_alloc && (oldsize + next_size) >= newsize){
            /*Merge cur block with next block*/
            size_t ttl_size = oldsize + next_size;
            PUT(HDRP(bp), PACK(ttl_size, 1));    // Update header(1)
            PUT(FTRP(bp), PACK(ttl_size, 1));    // Update footer(1)
            return bp;
        }
        else{
            /*Allocate new block*/
            void *new_bp = mm_malloc(newsize);
            if (new_bp == NULL){
                return NULL;}
            memcpy(new_bp, bp, oldsize);        // Copy old data to new block
            mm_free(bp);                        // Free old block
            return new_bp;
        }
    }
}

void *mm_realloc_nouse(void *ptr, size_t size)
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

/*Free allocated block and merge with next free blocks if possible*/
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1: if prev, next block allocated -> no merge
    if(prev_alloc && next_alloc){
        return bp;
    }
    // case 2: if prev allocated & next free -> merge curr+next
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // case 3: if prev free & next allocated -> merge prev+curr
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // case 4: if prev, next free -> merge prev+curr+next
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}