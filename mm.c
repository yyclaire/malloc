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
 *
 * Implementation: I used seglist as the data structure for my malloc,
 * and each list are indexed from 1-SEGLIST_SIZE, with each containing
 * size of blocks from 2^index to 2^(index+1). In each list the blocks 
 * are sorted according to their memory address in an ascending order. 
 * Init includes initilization of the heap and the seglist, coalesce is
 * only called when free is called, and realloc is implemented according
 * to the lab doc given. mm_check implemented with several helper functions.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* helper header */
#include <stdbool.h>

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "dqyy",
    /* First member's full name */
    "Diqiu Zhou",
    /* First member's WUSTL key */
    "zhoudiqiu",
    /* Second member's full name (leave blank if none) */
    "Yuan Yue",
    /* Second member's WUSTL key (leave blank if none) */
    "yuanyue"
};


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define SEGLIST_SIZE 40     /* Number of seglists */


/* Macros copied from PPT/book */
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                  

/* Given block ptr bp, compute address of its header and footer */
#define HEAD(bp)       ((char *)(bp) - WSIZE)                      
#define FOOT(bp)       ((char *)(bp) + GET_SIZE(HEAD(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
//line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
//line:vm:mm:prevblkp

/* Given block ptr bp, compute size/previous block/next block. */
#define SIZE(bp)      (GET_SIZE(HEAD(bp)))
#define ALLOC(bp)     (GET_ALLOC(HEAD(bp)))
#define PREV_SIZE(bp) (GET_SIZE((char *)(bp) - DSIZE))
#define PREV_ALLOC(bp) (GET_ALLOC((char *)(bp) - DSIZE))
#define NEXT_SIZE(bp) (GET_SIZE((char *)(bp) + SIZE(bp) - WSIZE))
#define NEXT_ALLOC(bp) (GET_ALLOC((char *)(bp) + SIZE(bp) - WSIZE))

/* Given block ptr bp, compute the address of the pre/suc block*/
#define PRE(bp)      ((char *)(bp) - GET(bp))
#define SUC(bp)      ((char *)(bp) + GET((char *)(bp) + WSIZE))

/* Given block ptr bp, change pred/succ */
#define PUT_PRED(bp, pre)  PUT(bp, (unsigned int)((char *)(bp) - (char*)(pre)))
#define PUT_SUCC(bp, suc)  PUT((char *)(bp)+WSIZE,(unsigned int)((char*)(suc) \
                               - (char *)(bp)))

/* variables created by myself */
/* various sizes of free list */
#define SIZE1 (1<<4)
#define SIZE2 (1<<5)
#define SIZE3 (1<<6)
#define SIZE4 (1<<7)
#define SIZE5 (1<<8)
#define SIZE6 (1<<9)
#define SIZE7 (1<<10)
#define SIZE8 (1<<11)
#define SIZE9 (1<<12)

static char *heap_listp = NULL;  
static size_t *list_head;  /* point to every list head */
static size_t *list_tail;  /* point to every list tail */

static void *extend_heap(size_t asize);    
static void *place(void *bp, size_t asize);
static void *find_fit(size_t asize);      
static void *coalesce(void *bp);         
static int get_index(size_t size);
static void *insert_block(void *bp);
static void delete_block(void *bp);
static void seglist_init(int size, size_t *head, size_t *tail);

static void print_block(void *bp);          
static void check_block(void *bp);         
static void check_freelist();
       
/*
 * mm_init - initialize the heap
 */
int mm_init(void) 
{
    /* some code here copied from the book */
    /* creat the initial empty heap */
    if ((heap_listp = mem_sbrk(SEGLIST_SIZE * DSIZE + 4*WSIZE)) == (void *)-1) 
        return -1;
    
    list_head = (size_t *)heap_listp;
    list_tail = (size_t *)(heap_listp + SEGLIST_SIZE / 2 * DSIZE);
    /* init of seglist */
    seglist_init(SEGLIST_SIZE/2, list_head, list_tail);
    heap_listp += SEGLIST_SIZE * DSIZE;   
    /* copied from the book */
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));     /* Epilogue header */  
    heap_listp += 2 * WSIZE;
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * seglist_init - helper func to initialize the seglist.
 *
 */
static void seglist_init(int size, size_t *head, size_t *tail) {
    /* easy init */
    int i;
    for (i = 0; i < size; i++) {
        head[i] = (size_t)NULL;
        tail[i] = (size_t)NULL;
    }
    return;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size) 
{
    size_t asize;
    char *bp;      
    
    /* Adjust block size  */
    if (size > DSIZE) {                    
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE); 
    }                                
    else {
        asize = DSIZE * 2;
    }

    /* seach for a fit */
    bool fit_found = ((bp = find_fit(asize)) != NULL);
    if (fit_found) {
        bp = place(bp, asize);
        return bp;
    }
    /* extend heap if we can't fit the block in */
    bool bp_is_NULL = ((bp = extend_heap(MAX(asize, CHUNKSIZE))) == NULL);
    if (bp_is_NULL) {
        /* extend_heap fails */
        return NULL;
    }else{
        /* placable after extend_heap */
        place(bp, asize);
        return bp;
    }  
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    /* ignore the illegal requests */
    if( bp == NULL) {
        return;
    }
    /* cope with the foot and head before coalesce */
    PUT(FOOT(bp), PACK(SIZE(bp), 0));
    PUT(HEAD(bp), PACK(SIZE(bp), 0));
    /* first insert,then coalesce */
    coalesce(insert_block(bp));
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    size_t asize;
    size_t freesize;
    char *bpnext;
    char *next;
    void *newptr;

    /* If oldptr is NULL, it is just malloc */
    bool ptr_is_NULL = (ptr == NULL);
    if (ptr_is_NULL) {
        return mm_malloc(size);
    }
    
    /* If size == 0, it is just free */
    bool size_is_zero = (size == 0);
    if (size_is_zero) {
        mm_free(ptr);
        return NULL;
    }
    /* else it is realloc */
    /* adjust the size and bools to indicate te status */
    oldsize = SIZE(ptr);
    asize = ALIGN(size + DSIZE);
    bool oldsize_larger = (oldsize >= asize);
    bool diff_smaller = (oldsize - asize < (DSIZE) * 2);
    bool next_not_alloc = (!NEXT_ALLOC(ptr));
    /* compute the new pointer size and see if it is smaller */
    bool newsize_smaller = (!NEXT_ALLOC(ptr) && NEXT_SIZE(ptr)+oldsize>=asize);
    /* newsize smaller */
    if (newsize_smaller) { 
        next = NEXT_BLKP(ptr);
        delete_block(next);
        bool nextsize_larger = (SIZE(next) + oldsize - asize >= (DSIZE) * 2);
        if (!nextsize_larger) {
            PUT(HEAD(ptr), PACK(SIZE(next) + oldsize, 1));
            PUT(FOOT(ptr), PACK(SIZE(next) + oldsize, 1));
        }
        else {
            PUT(HEAD(ptr), PACK(SIZE(next) + oldsize, 1));
            PUT(FOOT(ptr), PACK(SIZE(next) + oldsize, 1));
            /* compute the free size */
            freesize = SIZE(next) + oldsize - asize;
            PUT(HEAD(ptr), PACK(asize, 1));
            PUT(FOOT(ptr), PACK(asize, 1));
            /* get next pointer */
            bpnext = NEXT_BLKP(ptr);
            PUT(HEAD(bpnext), PACK(freesize, 0));
            PUT(FOOT(bpnext), PACK(freesize, 0));
            /* insert the next pointer back */
            insert_block(bpnext);
        }
        return ptr;
    }
    /* newsize larger */
    else if (oldsize_larger) {
        if (diff_smaller){
            PUT(HEAD(ptr), PACK(oldsize, 1));
            PUT(FOOT(ptr), PACK(oldsize, 1));
        }
        else {
            PUT(HEAD(ptr), PACK(oldsize, 1));
            PUT(FOOT(ptr), PACK(oldsize, 1));
            if (next_not_alloc){
                oldsize += NEXT_SIZE(ptr);
                delete_block(NEXT_BLKP(ptr));
            }
            PUT(HEAD(ptr), PACK(asize, 1));
            PUT(FOOT(ptr), PACK(asize, 1));
            /* get next pointer */
            bpnext = NEXT_BLKP(ptr);
            PUT(HEAD(bpnext), PACK(oldsize - asize, 0));
            PUT(FOOT(bpnext), PACK(oldsize - asize, 0));
            /* insert the next pointer back */
            insert_block(bpnext);
        }
        return ptr;
    }
    /* run malloc and memcpy after the realloc process */
    newptr = mm_malloc(size);
    memcpy(newptr, ptr, size);
    mm_free(ptr);
    return newptr;
}


/*
 * coalesce - coalesce the blocks
 */
static void *coalesce(void *bp) 
{   
    /* some code copied from the book */
    bool prev_alloc = PREV_ALLOC(bp);
    bool next_alloc = NEXT_ALLOC(bp);
    size_t size = SIZE(bp);
    /* both prev&next full then we do nothing */
    if (prev_alloc && next_alloc);
    /* both empty */              
    else if (!prev_alloc && !next_alloc) {      
        size += SIZE(PREV_BLKP(bp)) + SIZE(NEXT_BLKP(bp));
        delete_block(PREV_BLKP(bp));
        delete_block(NEXT_BLKP(bp));
        delete_block(bp);
        PUT(HEAD(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FOOT(NEXT_BLKP(bp)), PACK(size, 0));
        insert_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    /* prev empty */
    else if (!prev_alloc && next_alloc) {     
        size += SIZE(PREV_BLKP(bp));
        delete_block(PREV_BLKP(bp));
        delete_block(bp);
        PUT(HEAD(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FOOT(bp), PACK(size, 0));
        insert_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    /* next empty */
    else {                                    
        size += SIZE(NEXT_BLKP(bp));
        delete_block(NEXT_BLKP(bp));
        delete_block(bp);
        PUT(HEAD(bp), PACK(size, 0));
        PUT(FOOT(bp), PACK(size, 0));
        insert_block(bp);
    }
    return bp;
}

/* 
 * place - place the block onto the heap 
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = SIZE(bp);   
    void *next;
    delete_block(bp);
    
    bool block_smaller = ((csize - asize) < (DSIZE) * 2);
    /* if the block is smaller then just put it in */
    if (block_smaller) { 
        PUT(HEAD(bp), PACK(csize, 1));
        PUT(FOOT(bp), PACK(csize, 1));
    } else {
        /* insert to the next seglist if block is not smaller */
        PUT(HEAD(bp), PACK(csize, 1));
        PUT(FOOT(bp), PACK(csize, 1));
        PUT(HEAD(bp), PACK(asize, 1));
        PUT(FOOT(bp), PACK(asize, 1));
        next = NEXT_BLKP(bp);
        PUT(HEAD(next), PACK(csize-asize, 0));
        PUT(FOOT(next), PACK(csize-asize, 0));
        insert_block(next);
    }
    return bp;
}

/* 
 * find_fit - method to find a block that can hold the current block.
 */
static void *find_fit(size_t asize)
{
    void *bp;
    int i;
    for (i = get_index(asize); i <= SEGLIST_SIZE/2 - 1; i++) {
        /* no free block */
        bool head_null = ((void *)list_head[i] == NULL);
        if (head_null) {
            continue;
        }
        bp = (char *)list_head[i];
        while (true) {
            /* find a fit */
            bool bp_larger = (SIZE(bp) >= asize);
            if (bp_larger) {
                return bp;
            }
            /* tail reached */
            bool tail_is_bp = (bp == (void *)list_tail[i]);
            if (tail_is_bp) {
                break;
            }
            bp = SUC(bp);
        }
    }
    return NULL;
}


/* 
 * insert_block - insert block to free list, use the address of the block to determine the order
 */
static inline void *insert_block(void *bp){
    /* determine which list to go*/
    int i = get_index(SIZE(bp));
    char *tmp;
    bool head_not_null = ((void *)list_head[i] != NULL);
    if (head_not_null) {
        /* insert behind the tail*/
        bool behind_head = ((size_t)(bp) > list_tail[i]);
        bool ahead_head = ((size_t)(bp) < list_head[i]);
        if (behind_head) {
            PUT_PRED(bp, list_tail[i]);
            PUT_SUCC(list_tail[i], bp);
            list_tail[i] = (size_t)bp;
        }
        /* insert in front of the head*/
        else if (ahead_head) {
            PUT_SUCC(bp, list_head[i]);
            PUT_PRED(list_head[i], bp);
            list_head[i] = (size_t)bp;
        }
        /* ordinary situation*/
        else {
            tmp = (char *)list_head[i];
            while (SUC(tmp) < (char *)bp) {
                tmp = SUC(tmp);
            }
            PUT_PRED(bp, tmp);
            PUT_SUCC(bp, SUC(tmp));
            PUT_PRED(SUC(tmp), bp);
            PUT_SUCC(tmp, bp);
        }
    } else {
        /* an empty list, set up the list */
        list_head[i] = list_tail[i] = (size_t)bp;
    }
    return bp;
}
/* 
 *  delete_block - delete a newly allocated block in free list
 */
static inline void delete_block(void *bp){

    int i = get_index(SIZE(bp));

    bool delete_tail = ((size_t)(bp) == list_tail[i]);
    bool delete_head = ((size_t)(bp) == list_head[i]);
    bool only_one_node = (list_head[i] == list_tail[i]);

    if (only_one_node) { 
        /* delete the only node in the list*/
        list_tail[i] = (size_t)NULL;
        list_head[i] = (size_t)NULL;
    } else if (delete_tail) {
        /* delete the tail*/
        list_tail[i] = (size_t)PRE(bp);
    } else if (delete_head) {
        /* delete the head*/
        list_head[i] = (size_t)SUC(bp);
    } else {                 
        /* delete a node in the middle */
        PUT_PRED(SUC(bp), PRE(bp));
        PUT_SUCC(PRE(bp), SUC(bp));
    }
}

/*
 * get_index - get the target list with proper size.
 */
static inline int get_index(size_t size){
    if (size <= SIZE1) {
        return 0;
    } else if (size <= SIZE2) {
        return 1;
    } else if (size <= SIZE3) {
        return 2;
    } else if (size <= SIZE4) {
        return 3;
    } else if (size <= SIZE5) {
        return 4;
    } else if (size <= SIZE6) {
        return 5;
    } else if (size <= SIZE7) {
        return 6;
    } else if (size <= SIZE8) {
        return 7;
    } else if (size <= SIZE9) {
        return 8;
    } else {
        return 9;
    }
}

/* 
 * extend_heap - extend heap with free block and return its block pointer.
 */
static void *extend_heap(size_t asize) 
{
    char *bp = (char *)mem_heap_hi() - 3;
    char *end = (char *)mem_heap_hi() - 3;
    bool is_end = (GET_ALLOC(end));
    if (is_end) {
        if ((bp = mem_sbrk(asize)) == (void *)-1) {
            return NULL;
        }
    } else {
        if ((bp = mem_sbrk(asize - GET_SIZE(end))) == (void *) - 1) {
            return NULL;
        }
        bp = end - GET_SIZE(end) + DSIZE;
        delete_block(bp);
    }   
    /* initialize free block header/footer and the epilogue header */
    PUT(HEAD(bp), PACK(asize, 0));         /* Free block header */  
    PUT(FOOT(bp), PACK(asize, 0));         /* Free block footer */  
    PUT(HEAD(NEXT_BLKP(bp)), PACK(0, 1));  /* New epilogue header */ 
    /* extend new free block, insert */
    return insert_block(bp);
}

/* 
 * mm_check - check of the heap for consistency.
 */
void mm_check(int number_of_lines) {
    void *bp = heap_listp;
    bool pro_is_alloc = ALLOC(heap_listp);
    bool pro_size_right = (SIZE(heap_listp) == DSIZE);

    /* check heap list first*/
    printf("Heap (%p):\n", heap_listp);
    if (!pro_size_right || !pro_is_alloc) {
        printf("Mistake in prologue header.\n");
    }
    check_block(heap_listp);
    if (number_of_lines) {
        print_block(bp);
    }
    while (SIZE(bp) > 0) {
        if (number_of_lines) {
            print_block(bp);
        }
        check_block(bp);
        bp = (char *)NEXT_BLKP(bp);
    }

    bool epi_is_alloc = GET_ALLOC(HEAD(bp));
    bool epi_size_right = (SIZE(bp) == 0);

    if (!(epi_size_right && epi_is_alloc)) {
        printf("Mistake in epilogue header.\n");
    }
    /* then check free list */
    printf("Checking free list.\n");
    check_freelist();
}

/* 
 * print_block - print the status of a block.
 */
static void print_block(void *bp)
{
    size_t size, alloc;
    size = SIZE(bp);
    alloc = ALLOC(bp);

    bool line_end = (size == 0);
    if (line_end) {
        printf("%p: EOL\n", bp);
        return;
    }
    printf("%p: alloc/free: %c size: %d\n", bp, (alloc ? 'a' : 'f'),(int)size);
}

/*
 * check_block - check the correctness of a block.
 */
static void check_block(void *bp)
{
    bool is_aligned = ((size_t)ALIGN(bp) == (size_t)bp);
    if (!is_aligned) {
        printf("%p is not correctly aligned.\n", bp);
    }

    bool head_foot_match = (GET(HEAD(bp)) == GET(FOOT(bp)));
    if (!head_foot_match) {
        printf("Header and footer does not match correctly.\n");
    }
}

/*
 * check_freelist - check the consistency and correctness of the free lists
 */
static void check_freelist()
{
    char *tmp;
    int i = 0;
    while (i < SEGLIST_SIZE/2) {
        tmp = (char *)list_head[i];
        bool tmp_is_null = (tmp == NULL);
        if (tmp_is_null) {
            continue;
        }
        bool head_in_heap = (void *)list_head[i] <= mem_heap_hi() && \
                            (void *)list_head[i] >= mem_heap_lo();
        bool tail_in_heap = (void *)list_tail[i] <= mem_heap_hi() && \
                            (void *)list_tail[i] >= mem_heap_lo();
        if (tail_in_heap & head_in_heap) {
            int loop_continue = 1;
            while (loop_continue) {
                print_block(tmp);
                check_block(heap_listp);
                bool blk_allocated = ALLOC(tmp);
                bool right_link = (tmp == (char *)list_tail[i] || \
                                   PRE(SUC(tmp)) == tmp);
                bool right_tail = (tmp == (char *)list_tail[i]);
                if (blk_allocated) {
                    printf("Allocated block is found in free list.\n");
                }
                if (!right_link) {
                    printf("Mistake in linking.\n");
                }
                if (right_tail) {
                    break;
                }
                tmp = SUC(tmp);
            }
        } else {
            printf("Header or footer is out of boundary.\n");
        }
        i += 1;
    }
}

