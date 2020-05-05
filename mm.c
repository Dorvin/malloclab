  
/*
 * mm.c - malloc using segregated free list with combination of LIFO & first fit
 * 
 * Notice: [WSIZE]
 * 
 * Allocated Block: [size + allocation(LSB)][payload][payload]...[padding][padding][size + allocation(LSB)]
 * Free Block: [size + allocation(LSB)][pointer to prev in seg list][pointer to next in seg list][]...[][size + allocation(LSB)]
 * 
 * Structure of Segregated Free List: there are 10 class according to size, described in size_to_index function.
 * Each block is located in first position of appropraite free list.
 * It is simillar to Stack, that is LIFO
 * 
 * when finding free block to allocate, I used appropraite class according to it's size.
 * I incremented seg_index when there is no available free block until SEG_SIZE
 * In each free list, I used first fit strategy 
 * 
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros from textbook */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
// FTRP require Header of this block to be right value
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
// NEXT_BLKP require Header of this block to be right value
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// PREV_BLKP require Footer of prev block to be right value
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// constants and macros for free list
#define SET_PREV(bp, prev_bp)   (*((char**)(bp)) = prev_bp)
#define SET_NEXT(bp, next_bp)   (*((char**)(bp + WSIZE)) = next_bp)
#define GET_PREV(bp)            (*(char**)(bp))
#define GET_NEXT(bp)            (*(char**)(bp + WSIZE))

#define SEG_SIZE 10
#define GET_SEG_LIST_HDR(root, index)  *((char **)root+index)

// prototype of functions
static int mm_check(void);

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

static void insert_to_free_list(void *ptr);
static void delete_from_free_list(void *ptr);

static int size_to_index(size_t size);

/* global variables */
// point to prolog block
static char *heap_listp;
// segregated lists
static char *seg_lists;

/* 
 * mm_init - initialize the malloc package and make space for seg_lists, using mem_sbrk
 */
int mm_init(void)
{
    int index;
    seg_lists = mem_sbrk(SEG_SIZE * WSIZE);
    for(index = 0; index < SEG_SIZE; index++){
        GET_SEG_LIST_HDR(seg_lists, index) = NULL;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by finding appropraite free block in seg_lists.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0){
        return NULL;
    }

    if(size <= DSIZE){
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        //consistency check...
        //mm_check();
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    //consistency check...
    //mm_check();
    return bp;
}

/*
 * mm_free - Freeing a block that does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    if(ptr == NULL){
        return;
    }
    if(ptr < mem_heap_lo() || mem_heap_hi() < ptr){
        return;
    }
    if(GET_ALLOC(HDRP(ptr)) != 1){
        return;
    }
    if(GET(HDRP(ptr)) != GET(FTRP(ptr))){
        return;
    }
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);

    //consistency check...
    //mm_check();
}

/*
 * mm_realloc - Reallocate block, Implemented in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t asize;

    if(ptr == NULL){
        return mm_malloc(size);
    }
    if(size == 0){
        mm_free(ptr);
        return NULL;
    }
    if(ptr < mem_heap_lo() || mem_heap_hi() < ptr){
        return mm_malloc(size);
    }
    if(GET_ALLOC(HDRP(ptr)) != 1){
        return mm_malloc(size);
    }
    if(GET(HDRP(ptr)) != GET(FTRP(ptr))){
        return mm_malloc(size);
    }

    if(size <= DSIZE){
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if(asize <= GET_SIZE(HDRP(oldptr))){
        place(oldptr, asize);
        //consistency check...
        //mm_check();
        return oldptr;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    memcpy(newptr, oldptr, GET_SIZE(HDRP(oldptr)) - DSIZE);
    mm_free(oldptr);
    return newptr;
}

/* 
 * extend_heap - extend heap using mem_sbrk
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * coalesce - coalesce continuous free blocks, using footer and header
 * while deleting and inserting free blocks to seg lists
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void *next = NEXT_BLKP(bp);
    void *prev = PREV_BLKP(bp);

    // Case 1
    // nothing is free
    if (prev_alloc && next_alloc) {
        insert_to_free_list(bp);
        return bp;
    }

    // Case 2
    // only next is free
    else if (prev_alloc && !next_alloc) {
        delete_from_free_list(next);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        insert_to_free_list(bp);
    }

    // Case 3
    // only prev is free
    else if (!prev_alloc && next_alloc) {
        delete_from_free_list(prev);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_to_free_list(bp);
    }

    // Case 4
    // both are free
    else {
        delete_from_free_list(prev);
        delete_from_free_list(next);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_to_free_list(bp);
    }

    return bp;
}

/*
 * place - place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed the minimum block size.
*/
static void place(void *bp, size_t asize)
{
    delete_from_free_list(bp);
    int origin_size = GET_SIZE(HDRP(bp));
    int remain_size =  origin_size - asize;
    if(remain_size >= 2 * DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remain_size, 0));
        PUT(FTRP(bp), PACK(remain_size, 0));
        insert_to_free_list(bp);
    } else {
        PUT(HDRP(bp), PACK(origin_size, 1));
        PUT(FTRP(bp), PACK(origin_size, 1));
    }
}

/* 
 * find_fit - find approprate free block in seglist according to size, using first fit.
 */
static void *find_fit(size_t asize)
{
    int seg_index = size_to_index(asize);
    void *blockp;
    while(seg_index < SEG_SIZE){
        blockp = GET_SEG_LIST_HDR(seg_lists, seg_index);
        while(blockp != NULL){
            if(!GET_ALLOC(HDRP(blockp)) && (GET_SIZE(HDRP(blockp)) >= asize)){
                return blockp;
            }
            blockp = (void *)GET_NEXT(blockp);
        }
        seg_index++;
    }
    return NULL;
}

/* 
 * insert_to_free_list - insert to approprate seg_list using size_to_index.
 * Insert to firsit position of linked list.
 */
static void insert_to_free_list(void *ptr)
{
    int seg_index = size_to_index(GET_SIZE(HDRP(ptr)));
    void *list_hdr = GET_SEG_LIST_HDR(seg_lists, seg_index);
    SET_PREV(ptr, NULL);
    SET_NEXT(ptr, list_hdr);
    if(list_hdr != NULL){
        SET_PREV(list_hdr, ptr);
    }
    GET_SEG_LIST_HDR(seg_lists, seg_index) = ptr;
}

/* 
 * delete_from_free_list - delete from approprate seg_list using size_to_index.
 */
static void delete_from_free_list(void *ptr)
{
    void *prev = (void*)GET_PREV(ptr);
    void *next = (void*)GET_NEXT(ptr);
    int seg_index = size_to_index(GET_SIZE(HDRP(ptr)));
    if(prev != NULL){
        SET_NEXT(prev, next);
    } else {
        GET_SEG_LIST_HDR(seg_lists, seg_index) = next;
    }
    if(next != NULL){
        SET_PREV(next, prev);
    }
}

/* 
 * size_to_index - divide size into 10 classes.
 */
static int size_to_index(size_t size)
{
    if(size <= 64){
        return 0;
    } else if(size <= 128){
        return 1;
    } else if(size <= 256){
        return 2;
    } else if(size <= 512){
        return 3;
    } else if(size <= 1024){
        return 4;
    } else if(size <= 2048){
        return 5;
    } else if(size <= 4096){
        return 6;
    } else if(size <= 8192){
        return 7;
    } else if(size <= 16384){
        return 8;
    } else {
        return 9;
    }
}

/* 
 * mm_check - check heap consistency by checking coalescing and allocation bit, looking whole seg_lists
 */
static int mm_check(void)
{
    int err_count = 0;
    int seg_index = 0;
    void *list_hdr;
    while(seg_index < SEG_SIZE){
        list_hdr = GET_SEG_LIST_HDR(seg_lists, seg_index);
        while(list_hdr != NULL){
            if(GET_ALLOC(HDRP(list_hdr))){
                printf("err: allocated block is located in free list\n");
                err_count++;
            }
            if(!GET_ALLOC(FTRP(PREV_BLKP(list_hdr))) || !GET_ALLOC(HDRP(NEXT_BLKP(list_hdr)))){
                printf("err: coalescing has failed\n");
                err_count++;
            }
            list_hdr = GET_NEXT(list_hdr);
        }
        seg_index++;
    }
    if(err_count == 0){
        return 1;
    } else {
        return 0;
    }
}