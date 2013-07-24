/*
 * mm.c
 *
 * Napat Luevisadpaibul
 * ID:nluevisa
 * This solution uses segregate free list. Allcoate block consists of header and footer.
 * Free block consist of header, pointer to previosl free block, pointer to next free block and footer.
 * There are MAX_CLASS number of class starting with Class 0, payload of 1-8 byte size, to Class MAX_CLASS,
 * payload of more than 2^(MAX_CLASS+1). Each class have payload in range of 2^(CLASS INDEX+1) - 2^(CLASS_INDEX+2)
 * eg. if we have 4 classes, payload range is (class1,class2,class3,class4) = ( 1-8 , 9-16 , 17-32 , >32 )
 * Plolog contain |Header| ptr to class 1| ptr to class 2|...|ptr to class MAX_CLASS|Footer
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>

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
#define MAX_CLASS   4       /* Maximum number of class */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    
//#define PUTD(p, val) (*(long *)(p) = (val))
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
#define NEXT_FREEP(bp)  (*(char **)(bp + DSIZE))




/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *free_listp = 0;  /* Pointer to first free block */
static int current_class = 0;

//#define CLASSP(class)  (char *)(heap_listp + WSIZE*(class-1)) //pointer to class in prolog
//#define HEAD_CLASSP(class)  (*(char **)(heap_listp + WSIZE*(class-1)))
#define SET_HEAD_CLASSP(bp,class) (PUT(heap_listp + WSIZE*(class-1), (size_t)bp))


/* Function prototypes for internal helper routines */
static inline void *extend_heap(size_t words);
static inline void place(void *bp, size_t asize);
static inline void *find_fit(size_t asize);
static inline void *coalesce(void *bp);
static void print_block(void *bp);
static void check_heap(int verbose);
static void check_block(void *bp);
static void unit_test();
static inline void insert_free_block(void *bp);
static inline void remove_free_block(void *bp);
static inline int find_minimum_class(int asize);
//static inline void *link_head(int class);

static inline void *get_head_classp(int class)
{
    /*size_t *address_to_hold_pointer = (size_t *)(heap_listp + WSIZE*(class-2));
    size_t *head_pointer;
    dbg_printf("address to hold pointer is %p\n",address_to_hold_pointer);
    if( *address_to_hold_pointer == 0 )
    {
        dbg_printf("address of head ponter is 0");
        return NULL;
    }
    printf("value in that address: %zu\n",*address_to_hold_pointer);
    
    head_pointer = (size_t *)(*address_to_hold_pointer);

    //head_pointer = *(unsigned int **)(heap_listp + WSIZE*(class-1));
    dbg_printf("head pointer is %p\n",head_pointer);
    */
    int index = class-1;
    void *head_pointer = (char *)(intptr_t)GET(heap_listp + (index * WSIZE));
    if(head_pointer == NULL)
    {
        return NULL;
    }
    
    head_pointer = (char *)(intptr_t)((unsigned long)head_pointer + 0x800000000);
    dbg_printf("head pointer is %p\n",head_pointer);
    return head_pointer;
    
}


/* this function is used for unit test only */
static void unit_test(){
    /* test find_minimum_class
    printf("%d \n",find_minimum_class(3)); //1
    printf("%d \n",find_minimum_class(8)); //1
    printf("%d \n",find_minimum_class(12)); //2
    printf("%d \n",find_minimum_class(18)); //3
    printf("%d \n",find_minimum_class(32)); //3
    printf("%d \n",find_minimum_class(36)); //4
    */
    
    // test CLASSP
    /*
    printf("%p\n",CLASSP(1));
    printf("%p\n",CLASSP(2));
    printf("%p\n",CLASSP(3));
    */
    //char *bp;
    
    //PUT(0x800000008,0x80000000C);
    //PUT(0x80000000C,0x800000010);
    //bp = *(CLASSP(1));
    //printf("%p\n",bp);
    //mm_checkheap(1);
    
    //exit(0);
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    int i;
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(MAX_CLASS*WSIZE+2*MINIMUM)) == NULL)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + WSIZE, PACK(MAX_CLASS*WSIZE+2*WSIZE, 1));   /* Prolog Header */
        
    for(i=0; i< MAX_CLASS; i++)
    {
        //PUT(heap_listp + WSIZE, PACK(MINIMUM, 1));   /* Prolog Header */
        //PUT(heap_listp + DSIZE, 0);                  /* Prev pointer */
        //PUT(heap_listp + DSIZE + WSIZE, 0);          /* Next pointer */
        //PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1)); /* Prologue footer */
        PUT(heap_listp + DSIZE + WSIZE*i, 0);          /* pointer to start of free block of each class */
        
    }
    PUT(heap_listp + DSIZE + MAX_CLASS*WSIZE, PACK(MAX_CLASS*WSIZE+2*WSIZE, 1));   /* Prolog Footer */
    
    PUT(heap_listp + WSIZE + MAX_CLASS*WSIZE+2*WSIZE, PACK(0, 1));     /* Epilogue header */
    
    //heap_listp += (2*WSIZE);
    free_listp = heap_listp + (2*WSIZE);
    
    heap_listp += (2*WSIZE);
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    {
        return -1;
    }
    //mm_checkheap(1);
    unit_test();
    
    //exit(0);
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
    
    dbg_printf("Malloc of size %zu\n",asize);
    
    /* comment out adjust from implicit version
    if (size <= DSIZE)
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
    */
    
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);
        mm_checkheap(1);
        return bp;
    }
    
    dbg_printf("No fit found\n");
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;                                  
    place(bp, asize);
    
    mm_checkheap(1);
    
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    
    if(ptr == 0)
        return;
    
    dbg_printf("free %p\n",ptr);
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (free_listp == 0){
        mm_init();
    }
    
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    //mm_checkheap(1);
}

static inline void *coalesce(void *bp)
{
    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; //possible to remove second clause
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    dbg_printf("Begin coalesce at %p\n",bp);
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
    current_class = find_minimum_class(size);
    dbg_printf("current class = %d\n",current_class);
    insert_free_block(bp);
    //mm_checkheap(1);
    dbg_printf("end coalescing\n");
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
static inline void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    
    if(size < MINIMUM)
        size = MINIMUM;
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    dbg_printf("extend_heap of size %zu\n",size);
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    
    check_heap(1);
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                         
}

/*
 * Place block of asize bytes at start of free block bp
 * Then split if remainder is at least a minimum block size
 */

static inline void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    dbg_printf("begin place at %p, size %zu\n",bp,asize);
    if ((csize - asize) >= MINIMUM) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        remove_free_block(bp);
        
        
        bp = NEXT_BLKP(bp);
        dbg_printf("\n\n begin split block at %p, size %zu\n",bp,asize);
        
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

static inline void *find_fit(size_t asize)
{

    /* First fit search */
    dbg_printf("begin find fit of size %zu\n",asize);
    void *bp;
    
    int cp = find_minimum_class(asize);
    
    dbg_printf("minimum class is %d\n",cp);
    
    for(; cp <= MAX_CLASS; cp++ )
    {
         bp = get_head_classp(cp);
        printf("bp is %p\n",bp);
         if(bp == NULL)
         {
             dbg_printf("head of class %d is NULL\n",cp);
             continue;
         }
        for (; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
            //if (asize <= GET_SIZE(HDRP(bp))) {
            
            current_class = cp;
            dbg_printf("Found free blobk in class %d \n with pointer %p\n",cp,bp);
            dbg_printf("end find fit of size %zu\n",asize);
            return bp;
            //}
        }
    }
    
    // comment out explicit list version
    /*
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
     */
    current_class = 0;
    dbg_printf("end find fit of size %zu\n",asize);
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
    dbg_printf("Begin remove free block at %p\n",bp);
    /* If there's a previous block, set its next pointer to the next block.
	 * Otherwise, set this block to be the beginning of free list.
     */
	if (PREV_FREEP(bp))
    {
        dbg_printf("bp have previous pointer\n");
		NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
	}
    else
    {
		//free_listp = NEXT_FREEP(bp);
        //HEAD_CLASSP(current_class) = NEXT_FREEP(bp);
        dbg_printf("bp have no previous pointer set new head\n");
        SET_HEAD_CLASSP(NEXT_FREEP(bp),current_class);
	}
    check_heap(1);
    
}

/*
 * Inserts a block at the beginning of the free list
 */
static inline void insert_free_block(void *bp)
{
	/*NEXT_FREEP(bp) = free_listp; //Sets next ptr to start of free list
    PREV_FREEP(free_listp) = bp; //Sets previous pointer of current head to new block
	PREV_FREEP(bp) = NULL; // Sets previous pointer to NULL
	free_listp = bp; // Sets new block to be start of free list
    */
    dbg_printf("insert free block :%p \n",bp);
    dbg_printf("heap list :%p \n",heap_listp);
    
    //void *head = HEAD_CLASSP(current_class);
    //void *head = *(char **)heap_listp + WSIZE*3;
    //void *head2;
    //printf("cal address %p\n",heap_listp + WSIZE*3);
    //head1 = *(char **)(heap_listp + WSIZE*(class-1));
    //*(char **)(heap_listp + WSIZE*(class-1))
    
    void *head = get_head_classp(current_class);
    
    
    check_heap(1);
    
    if(head == NULL)
    {
        dbg_printf("this class has no head yet, make bp the head of the class\n");
        
    }
    else
    {
        dbg_printf("head of class %d is %p \n",current_class,head);
        NEXT_FREEP(bp) = head; //Sets next ptr to start of free list
        PREV_FREEP(head) = bp; //Sets previous pointer of current head to new block
    }
        
    
	PREV_FREEP(bp) = NULL; // Sets previous pointer to NULL
    SET_HEAD_CLASSP(bp,current_class); // Sets new block to be start of free list
    
    mm_checkheap(1);
    
    dbg_printf("finish insert free block :%p \n",bp);
}

/*
 * Find minimum class that can allocate for asize
 */
static inline int find_minimum_class(int asize)
{
    int upper=16,result = 2;
    int max = (1<<(MAX_CLASS+1));
    if(asize <= 8)
    {
        return 1;
    }
    if(asize > max)
    {
        return MAX_CLASS;
    }
    for (; upper <= max; upper*=2) {
        if (asize <= upper) {
            return result;
        }
        result++;
    }
    return 0;
}
/*
static inline void *link_head(int class){
    void *bp;
    bp = *(char **)GET(heap_listp + WSIZE*(class-1));
    return bp;
}
*/
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
    int i;
    //checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    int *p = (int *)bp;
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
     /* if it's allcoated bolck, print only header and footer info, otherwise including prev and next info*/
    
    if (halloc) {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),
        fsize, (falloc ? 'a' : 'f'));
        
        dbg_printf("block content :\n");
        for (i = 0; i < hsize; ++i)
        {
            dbg_printf("%p:%#x ", p+i,p[i]);
        }
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
   /*
    dbg_printf("End check entire heap\n");
    
    dbg_printf("Begin print free list\n");
    
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
        if (verbose)
            print_block(bp);
        check_block(bp);
    }
    
    dbg_printf("End print free list\n");
    */
    
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    check_heap(verbose);
}
