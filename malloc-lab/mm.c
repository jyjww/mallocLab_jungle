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

/*Get address of next free block*/
#define GET_SUCC(bp)    (*(void **)((char *)(bp) + WSIZE))      // address of next free block
#define GET_PRED(bp)    (*(void **)(bp))                        // address of prev free block

/*Declaration for static helper functions*/
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

/*Global pointer to first block*/
static void *free_listp = NULL;

/*mm_init - initialize the malloc package.*/
int mm_init(void)
{
    /*Create the initial empty heap*/
    if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;

    PUT(free_listp, 0);                          // Alignment padding
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(free_listp + (3*WSIZE), PACK(4*WSIZE, 0)); // First free block header

    // Free block payload: pred, succ
    *(void **)(free_listp + (4*WSIZE)) = NULL;     // pred
    *(void **)(free_listp + (5*WSIZE)) = NULL;     // succ

    PUT(free_listp + (6*WSIZE), PACK(4*WSIZE, 0)); // First free block footer
    PUT(free_listp + (7*WSIZE), PACK(0, 1));       // Epilogue header

    free_listp += (4*WSIZE);   // payload(pred) 위치를 가리켜야 함
    /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;           // actual size for allocation
    size_t extendsize;      // amount to extend heap if no fit
    char *bp;               // bp pointer

    /*Ignore req for zero bytes*/
    if (size == 0)
        return NULL;

    /*Adjust block size to include overhead and alignment req*/
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1))/ DSIZE);

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


static void *extend_heap(size_t words)
{
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
    void *bp = free_listp;

    /*Search from head of free list -> follow succ -> return same or bigger size block*/
    while(bp != NULL){
        if (GET_SIZE(HDRP(bp)) >= asize)
            return bp;
        bp = GET_SUCC(bp);
    }
    return NULL;    // No fit
}

static void place(void *bp, size_t size)
{
    // current block size
    remove_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp)); 

    if ((csize - size) >= (2*DSIZE)){
        /*Split block : allocate front part*/
        PUT(HDRP(bp), PACK(size, 1));      // Set header as allocated(1)
        PUT(FTRP(bp), PACK(size, 1));      // Set footer as allocated(1)
        
        /*Create new free block with remaining space*/
        void *new_bp = NEXT_BLKP(bp);
        PUT(HDRP(new_bp), PACK(csize - size, 0));      // Set header as free
        PUT(FTRP(new_bp), PACK(csize - size, 0));      // Set footer as free
        insert_free_block(new_bp);
    }
    else{
        /*Do not split : allocate entire block*/
        PUT(HDRP(bp), PACK(csize, 1));          // Set entire block header as allocated
        PUT(FTRP(bp), PACK(csize, 1));          // Set entire block footer as allocated
    }
}

/*Insert free block at start of free list (LIFO)*/
static void insert_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;                  // bp's succ = header block
    if (free_listp != NULL)                     // if free list not empty -> change head to new block
        GET_PRED(free_listp) = bp;
    // Update free list head to bp
    free_listp = bp;
}

/*Remove free block from free list*/
static void remove_free_block(void *bp)
{
    // If bp is head -> move head to bp's succ
    if (bp == free_listp){
        free_listp = GET_SUCC(free_listp);
        return;
    }
    // Set pred's succ to bp's succ
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    
    // If bp has succ -> update pred pointer
    if (GET_SUCC(bp) != NULL){
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
    }
}

/*mm_realloc - naive*/
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t cpySize;

    new_bp = mm_malloc(size);
    if(new_bp == NULL)
        return NULL;
    
    cpySize = GET_SIZE(HDRP(old_bp)) - DSIZE;
    if (size < cpySize)
        cpySize = size;
    memcpy(new_bp, old_bp, cpySize);
    mm_free(old_bp);
    return new_bp;
    
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
    
    if (prev_alloc && next_alloc) {          // case 1
        insert_free_block(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {     // case 2
        void *next_bp = NEXT_BLKP(bp);

        remove_free_block(next_bp);   // 여기는 ok (next가 free인게 확실)
        size += GET_SIZE(HDRP(next_bp));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {     // case 3
        void *prev_bp = PREV_BLKP(bp);

        remove_free_block(prev_bp);   // 여기도 ok (prev가 free인게 확실)
        size += GET_SIZE(FTRP(prev_bp));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev_bp), PACK(size, 0));
        bp = prev_bp;
    }
    else {                             // case 4
        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);

        remove_free_block(prev_bp);
        remove_free_block(next_bp);

        size += GET_SIZE(FTRP(prev_bp)) + GET_SIZE(HDRP(next_bp));

        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(next_bp), PACK(size, 0));
        bp = prev_bp;
    }
    insert_free_block(bp);
    return bp;
}
