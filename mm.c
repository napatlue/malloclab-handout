/*
 * mm.c
 *
 * Napat Luevisadpaibul
 * ID:nluevisa
 * This solution uses explicit free list. Allcoate block consists of header and foother.
 * Free block consist of header, pointer to previosl free block, pointer to next free block and footer.
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
    
    heap_listp = free_listp;
    
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
    
    if(ptr == 0)
        return;
    
    
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (free_listp == 0){
        mm_init();
    }
    
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    //mm_checkheap(1);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; //possible to remove second clause
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
	/* Case 1, coalesce with previous block */
	if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_free_block(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
    
	/* Case 2, coalesce with next block */
	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		bp = PREV_BLKP(bp);
		remove_free_block(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
    
	/* Case 3, coalesce with both previous and next block */
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
    
	//insert free block at the beginning of free list
    insert_free_block(bp);
    //mm_checkheap(1);
    
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
    
	/* If the size doesn't need to be changed, return original pointer */
	if (asize == oldsize)
		return oldptr;
    
	/* If the size needs to be decreased, shrink the block and
	 * return original pointer */
	if(asize <= oldsize)
	{
		size = asize;
        
		/* If the remaining space is not enough for a minimum free block size
		 * return the original pointer 
         */
		if(oldsize - size <= MINIMUM)
			return oldptr;
		PUT(HDRP(oldptr), PACK(size, 1));
		PUT(FTRP(oldptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(oldptr)), PACK(oldsize-size, 1));
        
        // free the remaing space after shrinking the block
		free(NEXT_BLKP(oldptr));
		return oldptr;
	}
    
	//If we can not fit the new block in the old block, then we need to allocate new free block elsewhere
    newptr = malloc(size);
    
	/* If malloc() fails,return NULL  */
	if(!newptr) {
		return 0;
	}
    
	/* Copy the old data. */
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);
    
	/* Free the old block. */
	free(oldptr);

    //mm_checkheap(1);
    return newptr;
}



/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
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
 * Place block of asize bytes at start of free block bp
 * Then split if remainder is at least a minimum block size
 */

static void place(void *bp, size_t asize)
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
{

    /* First fit search */
    void *bp;
    
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL; /* No fit */

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
/*
 * Remove free block pointed by bp
 */

static inline void remove_free_block(void *bp)
{
    /* If there's a previous block, set its next pointer to the next block.
	 * Otherwise, set this block to be the beginning of free list.
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
 * Inserts a block at the beginning of the free list
 */
static void insert_free_block(void *bp)
{
	NEXT_FREEP(bp) = free_listp; //Sets next ptr to start of free list
	PREV_FREEP(free_listp) = bp; //Sets previous pointer of current head to new block
	PREV_FREEP(bp) = NULL; // Sets previous pointer to NULL
	free_listp = bp; // Sets new block to be start of free list
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

/*
 * Print information of the block pointed by bp
 */
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
    int halloc = GET_ALLOC(HDRP(bp));    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; //possible to remove second clause
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    if (!in_heap(bp))
        printf("Error: %p is not in heap\n", bp);
    if (!aligned(bp))
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    
    /*
     * in case of free list check whether there are contiguous free block not properly coalesce
    */
    if (!halloc)
    {
        if (!prev_alloc) {
            printf("Error: %p previous block is free, should coalescing\n", bp);
        }
        if(!next_alloc)
        {
            printf("Error: %p next block is free, should coalescing\n", bp);
        }

    }
    
    
}

/*
 * checkheap - my check heap function
 */
void check_heap(int verbose)
{
    char *bp;
    
    dbg_printf("Begin check entire heap\n");
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    
    if ((GET_SIZE(HDRP(heap_listp)) != MINIMUM) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    check_block(heap_listp);

    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(verbose)
            print_block(bp);
        check_block(bp);
    }
    
    if (verbose)
        print_block(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    
    dbg_printf("End check entire heap\n");
    
    dbg_printf("Begin print free list\n");
    
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (verbose)
            print_block(bp);
        check_block(bp);
    }
    
    dbg_printf("End print free list\n");
    
    
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    check_heap(verbose);
}
