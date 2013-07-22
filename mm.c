/*
 * mm.c
 *
 * Napat Luevisadpaibul
 * ID:nluevisa
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MINIMUM     24      /* Minimum block size */

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
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Given free block ptr bp, compute address of next and previous free blocks */
#define PREV_FREEP(bp)  (*(char **)(bp))
#define NEXT_FREEP(bp)  (*(char **)(bp + DSIZE)) // possible change to WSIZE


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *free_listp = 0;  /* Pointer to first free block */


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void print_block(void *bp);
static void check_heap(int verbose);
static void check_block(void *bp);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(2*MINIMUM)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    
    
    PUT(heap_listp + WSIZE, PACK(MINIMUM, 1));   /* Prolog Header */
    PUT(heap_listp + DSIZE, 0);                  /* Prev pointer */
    PUT(heap_listp + DSIZE + WSIZE, 0);          /* Next pointer */
    PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1)); /* Prologue footer */
    
    
    PUT(heap_listp + WSIZE + MINIMUM, PACK(0, 1));     /* Epilogue header */
    
    //heap_listp += (2*WSIZE);
    free_listp = heap_listp + (2*WSIZE);
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
    if (free_listp == 0){ // instantiate free list
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    asize = MAX(ALIGN(size) + DSIZE, MINIMUM);
    
    /* comment out adjust from implicit version
    if (size <= DSIZE)
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
    */
    
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                 
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;                                  
    place(bp, asize);
    //mm_checkheap(1);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    /* $end mmfree */
    if(ptr == 0)
        return;
    
    /* $begin mmfree */
    size_t size = GET_SIZE(HDRP(ptr));
    /* $end mmfree */
    if (free_listp == 0){
        mm_init();
    }
    /* $begin mmfree */
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
	/* Case 1, extend the block leftward */
	if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_free_block(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
    
	/* Case 2, extend the block rightward */
	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		bp = PREV_BLKP(bp);
		remove_free_block(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
    
	/* Case 3, extend the block in both directions */
	else if (!prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_free_block(PREV_BLKP(bp));
		remove_free_block(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
    
	insert_free_block(bp);

    /* $begin mmfree */
    return bp;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;
    size_t asize = MAX(ALIGN(size) + DSIZE, MINIMUM);
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return mm_malloc(size);
    }
    
    /* Get the size of the original block */
	oldsize = GET_SIZE(HDRP(oldptr));
    
	/* If the size doesn't need to be changed, return orig pointer */
	if (asize == oldsize)
		return oldptr;
    
	/* If the size needs to be decreased, shrink the block and
	 * return the same pointer */
	if(asize <= oldsize)
	{
		size = asize;
        
		/* If a new block couldn't fit in the remaining space,
		 * return the pointer */
		if(oldsize - size <= MINIMUM)
			return oldptr;
		PUT(HDRP(oldptr), PACK(size, 1));
		PUT(FTRP(oldptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(oldptr)), PACK(oldsize-size, 1));
		free(NEXT_BLKP(oldptr));
		return oldptr;
	}
    
	newptr = malloc(size);
    
	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}
    
	/* Copy the old data. */
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);
    
	/* Free the old block. */
	free(oldptr);

    
    return newptr;
}


/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    
    if(size < MINIMUM)
        size = MINIMUM;
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;                                        
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                         
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MINIMUM) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        remove_free_block(bp);
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        
        remove_free_block(bp);
    }
}

static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    /* $end mmfirstfit */
    

    /* $begin mmfirstfit */
    /* First fit search */
    void *bp;
    
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL; /* No fit */
    /* $end mmfirstfit */

}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}

static inline void remove_free_block(void *bp)
{
    /* If there's a previous block, set its next pointer to the
	 * next block.
	 * If not, set the block's previous pointer to the prev block.
     */
	if (PREV_FREEP(bp))
    {
		NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
	}
    else
    {
		free_listp = NEXT_FREEP(bp);
	}
    PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
}

/*
 * insertAtFront - Inserts a block at the front of the free list
 * This function takes a block pointer of the block to add to the
 * free list as a parameter.
 */
static void insert_free_block(void *bp)
{
	NEXT_FREEP(bp) = free_listp; //Sets next ptr to start of free list
	PREV_FREEP(free_listp) = bp; //Sets current's prev to new block
	PREV_FREEP(bp) = NULL; // Sets prev pointer to NULL
	free_listp = bp; // Sets start of free list as new block
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

static void print_block(void *bp)
{
    int hsize, halloc, fsize, falloc;
    
    //checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
     /* if it's allcoated bolck, print only header and footer info, otherwise including prev and next info*/
    
    if (halloc) {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),
        fsize, (falloc ? 'a' : 'f'));
    }
    else{
        printf("%p: header: [%d:%c] prev:%p next:%p footer: [%d:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),
        PREV_FREEP(bp),
        NEXT_FREEP(bp),
        fsize, (falloc ? 'a' : 'f'));
    }
}

static void check_block(void *bp)
{
    if (!in_heap(bp))
        printf("Error: %p is not in heap\n", bp);
    if (!aligned(bp))
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void check_heap(int verbose)
{
    char *bp = heap_listp;
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    
    if ((GET_SIZE(HDRP(heap_listp)) != MINIMUM) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    check_block(heap_listp);
    
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (verbose)
            print_block(bp);
        check_block(bp);
    }
    
    if (verbose)
        print_block(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    check_heap(verbose);
}
