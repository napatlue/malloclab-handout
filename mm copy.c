/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
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

typedef unsigned int size_class;
typedef char byte;
typedef int word;
typedef void* heap_index;

#define FREE_LIST_SEGREGATION 256;

#define LIST_END (void*) 0  // List terminator
#define NUM_FREE_LISTS 40 // Number of segregated lists

#define FREE 0
#define ALLOC 1
#define HEADER_SIZE 8
#define FOOTER_SIZE 8
#define MIN_SIZE 24 // Header + footer + min block size (8)


/* We have prologue and epilogue blocks on either end to simplify coalescing.
 Each is an empty block. */
#define BOUNDARY_SIZE 0
#define MAKE_BOUNDARY(block) (PUT(HEADER(block),PACK(BOUNDARY_SIZE,ALLOC,ALLOC)))

// Tag is just the size, in bytes, of the "tag" of packed size and allocation information
#define TAG_SIZE 4
#define PACK(size, alloc, prev_alloc) ((size | alloc) | (prev_alloc << 1))

/* Manipulating words */
#define PUT(p, val) (*(word *)(p) = val)
#define GET(p)      (*(word *)(p))

/*
 * Macros for getting information about a block. In all functions, the block pointer bp
 * is assumed to point to the payload, ie, the pointer that malloc would return and free
 * would call.
 */
#define HEADER(bp)  ((void*)(bp) - HEADER_SIZE)
#define FOOTER(bp)  ((void*)(bp) + PAYLOAD_SIZE(bp))
#define PAYLOAD_FROM_HEADER(hp) ((void*) hp + HEADER_SIZE)

// Various ways of measuring block size
#define PAYLOAD_SIZE(bp)  (UNPACK_SIZE(HEADER(bp))) // Payload size of a block
#define PAD_SIZE(size) (size + HEADER_SIZE + FOOTER_SIZE) // Payload size -> block size
#define BLOCK_SIZE(bp) (PAD_SIZE(PAYLOAD_SIZE(bp))) // Actual space a block takes up
#define UNPACK_SIZE(tag) (GET(tag) & ~0x7) // Tag -> size

// Free/alloc status of blocks
#define IS_ALLOC(bp)    (GET(HEADER(bp)) & 0x1) // 1 for allocated, 0 for free
#define IS_FREE(bp)     (!IS_ALLOC(bp))
#define IS_PREV_ALLOC(bp) ((GET(HEADER(bp)) & 0x2) == 0x2)
#define IS_NEXT_ALLOC(bp) (IS_ALLOC(NEXT(bp)))

// Setting free/alloc status
#define MARK_ALLOC(bp)  (PUT(HEADER(bp),GET(HEADER(bp)) | 0x1))
#define MARK_FREE(bp)   (PUT(HEADER(bp),GET(HEADER(bp)) & ~0x1))
#define MARK_PREV_ALLOC(bp) (PUT(HEADER(bp), GET(HEADER(bp)) | 0x2))
#define MARK_PREV_FREE(bp)  (PUT(HEADER(bp), GET(HEADER(bp)) & ~0x2))

/*
 * SET_FREE and SET_ALLOC handle all the necessary bookkeeping of freeing /
 * allocating a block of memory. They update the free list, mark the free
 * bits, and mark the prev-allocated bit of the next block.
 */
#define SET_FREE(bp) {MARK_FREE(bp); MARK_PREV_FREE(NEXT(bp)); addToFreeList(bp);}
#define SET_ALLOC(bp) {deleteFromFreeList(bp); MARK_ALLOC(bp); MARK_PREV_ALLOC(NEXT(bp));}

/*
 * Heap traversal
 */
#define NEXT(bp) (bp + BLOCK_SIZE(bp))
#define PREV_FOOTER(bp) (HEADER(bp) - FOOTER_SIZE)
#define PREV(bp) (bp - PAD_SIZE(UNPACK_SIZE(PREV_FOOTER(bp))))

/*
 * Free list traversal
 */

// Get a pointer to the head of the free list (dereference to get head)
//#define FREE_LIST(class) ((void**) (heap_start + (log_2(class) - 3) * 4))

#define CLASS_TO_NUM(class) (class >> 5);
#define FREE_LIST(class) ((void**) (heap_start + (CLASS_TO_NUM(class) * 4)))

// Gets the head of the free list
#define GET_FREE_LIST(class) (*FREE_LIST_NUM(class))
#define SET_FREE_LIST(class,block) (*FREE_LIST_NUM(class) = block)

// Get the Nth free list (as opposed to the free list of size CLASS)
#define FREE_LIST_NUM(num) ((void**) (heap_start + num * 4))

// Traverse the free list
#define NEXT_FREE_BLOCK(bp) ((void**) ((void*) HEADER(bp) + TAG_SIZE))
#define PREV_FREE_BLOCK(bp) ((void**) ((void*) FOOTER(bp) + TAG_SIZE))
#define GET_NEXT_FREE_BLOCK(bp) (*NEXT_FREE_BLOCK(bp))
#define GET_PREV_FREE_BLOCK(bp) (*PREV_FREE_BLOCK(bp))
#define SET_NEXT_FREE_BLOCK(bp,next) (GET_NEXT_FREE_BLOCK(bp) = next)
#define SET_PREV_FREE_BLOCK(bp,prev) (GET_PREV_FREE_BLOCK(bp) = prev)


/* The amount of free space at the end of the heap
 (i.e., in the block preceding the epilogue block).
 0 if the last block on the heap is allocated. */
#define END_FREE_SPACE (IS_PREV_ALLOC(epilogue) ? 0 : BLOCK_SIZE(PREV(epilogue)))

void* heap_start;
void* prologue;
void* epilogue;

static void* find_segregated_fit(int size);
static size_class get_size_class(size_t size);
static void* alloc_new_block(size_t size);
static void update_payload_size(void* block, size_t new_size);
static void* split_block(void* block, size_t carve_size);
static void deleteFromFreeList(void* block);
static void* coalesce(void* block);
static void addToFreeList(void* block);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    // Start by allocating space for the free lists, the prologue, and the epilogue
    heap_start = mem_sbrk(NUM_FREE_LISTS * sizeof(void**) + 2*PAD_SIZE(BOUNDARY_SIZE));
    void** current_index = heap_start;
    
    // Initialize all list pointers to LIST_END
    int i;
    for (i = 0; i < NUM_FREE_LISTS; i++) {
        *current_index = LIST_END;
        current_index++;
    }
    
    // Initialize prologue and epilogue
    prologue = (void*) current_index + HEADER_SIZE; // We point to payload so our macros work
    MAKE_BOUNDARY(prologue);
    epilogue = prologue + PAD_SIZE(BOUNDARY_SIZE);
    MAKE_BOUNDARY(epilogue);
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    
    int newsize = ALIGN(size);
    
    // Start by checking the free lists for a block of size NEWSIZE
    void *p = find_segregated_fit(newsize);
    
    // If that fails, allocate room for NEWSIZE more bytes
    if (p == NULL)
        p = alloc_new_block(newsize);
    
    if (p == NULL)
        return p; // We're out of memory :(
    
    // Finalize allocation
    SET_ALLOC(p);
    
    return p;
}

/*
 * free
 */
void free (void *ptr) {
    // Bookkeeping to mark a block as free
    SET_FREE(ptr);
    
    // Coalesce in case neighboring blocks are also free
    coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size){
    
    void *old_ptr = oldptr;
    void *new_ptr;
    size_t old_size = PAYLOAD_SIZE(old_ptr);
    size_t new_size = ALIGN(size);
    int size_diff = new_size - old_size;
    
    // If ptr is null, call mm_malloc
    if (!oldptr){
        return mm_malloc(size);
    }
    
    // If size == 0, free
    else if (!size){
        mm_free(oldptr);
        return NULL;
    }
    
    // If we're dividing the block in half or smaller, split the block.
    // (Any smaller reduction isn't really worth the trouble)
    else if (new_size < old_size / 2){
        // Mark the current block as free and put it on a free list
        SET_FREE(old_ptr);
        
        // Split the block to the new size
        new_ptr = split_block(old_ptr, new_size);
        
        // Delete the newly resived block from the free list and allocate it
        SET_ALLOC(new_ptr);
        return new_ptr;
    }
    
    // If we're reallocing the same size or just something slightly smaller,
    // do nothing.
    else if (new_size <= old_size){
        return old_ptr;
    }
    
    
    
    // If we're reallocing more memory, check the next block
    else {
        
        void** prev = PREV(old_ptr);
        void** next = NEXT(old_ptr);
        int prev_free = IS_FREE(prev);
        int next_free = IS_FREE(next);
        int prev_size = PAYLOAD_SIZE(prev);
        int next_size = PAYLOAD_SIZE(next);
        
        /* If the surrounding blocks in the heap are free and big enough to hold
         the additional memory we want to allocate, combine the blocks */
        if ((next_free && next_size >= size_diff) ||
            (prev_free && prev_size >= size_diff) ||
            (next_free && prev_free && (prev_size + next_size) >= size_diff)){
            // Mark the current block as free and put it on a free list
            SET_FREE(old_ptr);
            
            /* Coalesce the block to combine with the surrounding blocks */
            new_ptr = coalesce(old_ptr);
            
            /* If the start of the block has changed, then the previous block
             was free and we are now starting there, so we want to copy
             the existing data */
            if (new_ptr != old_ptr)
                memcpy(new_ptr, old_ptr, old_size);
            
            /* Split the new block appropriately, delete it from its
             free list, and mark it as allocated before returning */
            new_ptr = split_block(new_ptr, new_size);
            SET_ALLOC(new_ptr);
            return new_ptr;
        }
        
        /* If we're requesting more space and that additional space isn't
         available in the surrounding blocks, we have to malloc a new block.
         Since a block that's growing out of its space is likely to grow again
         in the future, we save ourselves some trouble by allocating double the
         space next time. This simple optimization makes for huge performance
         increases on the provided traces, even if it might not always be ideal.
         */
        else {
            new_ptr = mm_malloc(new_size * 2); // Get new pointer
            if (new_ptr == NULL) // Return NULL if we are out of memory
                return NULL;
            memcpy(new_ptr, old_ptr, old_size); // Copy the old data
            mm_free(old_ptr); // Free the old block
            return new_ptr; // Return the new pointer
        }
    }
}
/*
 * Finds the first available free block whose payload size is >= REQUEST_SIZE.
 * Uses get_size_class to search the appropriate free list and runs a first-fit
 * search through that list, cascading up to larger free lists if necessary. If
 * all free lists are exhausted, return NULL. If a block is found, we split
 * if necessary and then return a pointer to the block.
 */
static void* find_segregated_fit(int size)
{
    // Check for valid input
    if (size <= 0)
        return NULL;
    
    size_class class = get_size_class(size);
    
    
    /* Loop through increasing free lists until we find a free block,
     starting with the appropriate list for request_size */
    void** list;
    for (list = FREE_LIST_NUM(class); (void*) list < HEADER(prologue); list++) {
        // The head of the free list
        void* current_block = *list;
        
        /* Traverse this free list looking for block of the requisite size.
         When we find it, split and return. */
        while (current_block != LIST_END) {
            
            if (PAYLOAD_SIZE(current_block) >= size)
                return split_block(current_block, size);
            
            current_block = GET_NEXT_FREE_BLOCK(current_block);
        }
    }
    
    /* If we haven't found an appropriate block in any free list searched,
     return NULL so mm_malloc will allocate a new block */
    return NULL;
}

/*
 * Takes a size, in bytes, and returns its size class. The size class
 * is just represented as the minimum size in that class, in bytes. We
 * may implement this as a macro if our size classes are very simple.
 */
static size_class get_size_class(size_t size) {
    // Find the lowest power of two
    return size/FREE_LIST_SEGREGATION;
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
 * Allocates room on the heap for SIZE more bytes. If there is already free
 * space at the end of the heap, it will ask for SIZE - FREE_SPACE and
 * coalesce to make a perfectly sized block. Handles the shifting of epilogue
 * to the end of the heap.
 *
 * Returns NULL if no memory is available and a pointer to the newly allocated
 * block otherwise.
 */
static void* alloc_new_block(size_t size) {
    size_t block_size = PAD_SIZE(size);
    
    size_t size_needed = block_size - END_FREE_SPACE;
    
    // Allocate SIZE more bytes of memory, plus header and footer, minus any free space already at end
    void* p = mem_sbrk(size_needed);
    
    // New free zone starts where the old epilogue was
    p = epilogue;
    MARK_FREE(p);
    update_payload_size(p, size_needed - 16);
    addToFreeList(p);
    
    // Scoot epilogue over to its new home
    epilogue += size_needed;
    MAKE_BOUNDARY(epilogue);
    MARK_PREV_FREE(epilogue);
    
    // Coalesce
    p = coalesce(p);
    
    // Split if necessary, then return
    return split_block(p, size);
}

/*
 * Takes a BLOCK and sets its payload size, in header and footer, to NEW_SIZE.
 * DOES NOT put it in a free list--caller should handle this.
 */
static void update_payload_size(void* block, size_t new_size) {
    word new_tag = PACK(new_size,IS_ALLOC(block),IS_PREV_ALLOC(block));
    PUT(HEADER(block),new_tag);
    PUT(FOOTER(block),new_tag);
}

/*
 * Takes a BLOCK of sufficient size (or returns the original block if
 * this condition is not met) and splits it into two pieces, the first
 * of which has size CARVE_SIZE.
 *
 * split_block handles all free list operaitons internally. The block to be
 * split is removed from its free list and two resulting blocks are pushed onto
 * their respective list. This could perhaps be optimized more, since splitting
 * is usually called before allocating the first block, but we felt this makes
 * for a cleaner interface. It also updates the headers and footers of both
 * blocks as necessary.
 */
static void* split_block(void* block, size_t carve_size) {
    size_t initial_size = PAYLOAD_SIZE(block);
    // if we need to split
    if (initial_size >= carve_size + MIN_SIZE) {
        
        // Delete the original node from its old free list
        deleteFromFreeList(block);
        
        // Set the first block to its new size
        update_payload_size(block, carve_size);
        
        // Create the new free block and set its size
        void* new_block = NEXT(block);
        size_t new_size = initial_size - BLOCK_SIZE(block);
        update_payload_size(new_block, new_size);
        SET_FREE(new_block);
        
        // Add the blocks to the proper free lists
        addToFreeList(block);
        
    }
    
    return block;
}

/*
 * Deletes BLOCK from its free list by setting the pointers on either
 * side to hop over it.
 */
static void deleteFromFreeList(void* block) {
    void* prev = GET_PREV_FREE_BLOCK(block);
    void* next = GET_NEXT_FREE_BLOCK(block);
    
    // If we're deleting the head, update the free list pointer
    if (prev == LIST_END)
        SET_FREE_LIST(get_size_class(PAYLOAD_SIZE(block)), next);
    else
        SET_NEXT_FREE_BLOCK(prev,next);
    
    // If we're deleting the tail, we don't have to do anything more
    if (next != LIST_END)
        SET_PREV_FREE_BLOCK(next,prev);
}

/*
 * Takes a block to be freed and checks the blocks on either side of it,
 * combining with these blocks if they are free. Removes any blocks it
 * consolidates from their respective free lists. Sets the header and
 * footer of the new block it creates and returns a pointer to that
 * header.
 *
 * To make for a simple interface, coalesce handles all updates of the free
 * list and headers. Specifically, it deletes any blocks it consolidates from
 * their free lists and puts the new block that results onto its proper free
 * list.
 */
static void* coalesce(void* block) {
    int prev_alloc = IS_PREV_ALLOC(block);
    int next_alloc = IS_NEXT_ALLOC(block);
    size_t size = PAYLOAD_SIZE(block);
    
    // Case 1: Nothing to coalesces
    if (prev_alloc && next_alloc) {
        return block;
    }
    
    // Case 2: Coalesce with next block
    else if (prev_alloc) {
        void* next = NEXT(block);
        
        // Maintain free lists
        deleteFromFreeList(block);
        deleteFromFreeList(next);
        
        // Update header of BLOCK so that size stretches to encompass NEXT
        size += PAD_SIZE(PAYLOAD_SIZE(next));
        PUT(HEADER(block), PACK(size,FREE,IS_PREV_ALLOC(block)));
        PUT(FOOTER(next), PACK(size,FREE,IS_PREV_ALLOC(block)));
        
        addToFreeList(block);
        return block;
    }

    // Case 3: Coalesce with prev block
    else if (next_alloc) {
        void* prev = PREV(block);
        
        // Maintain free lists
        deleteFromFreeList(block);
        deleteFromFreeList(prev);
        
        // Update header of PREV so that size stretches to encompass BLOCK
        size += PAD_SIZE(PAYLOAD_SIZE(prev));
        PUT(FOOTER(block), PACK(size,FREE,IS_PREV_ALLOC(prev)));
        PUT(HEADER(prev), PACK(size,FREE,IS_PREV_ALLOC(prev)));
        
        addToFreeList(prev);
        return prev;
    }
    
    // Coalesce both ends
    else {
        void* prev = PREV(block);
        void* next = NEXT(block);
        
        // Maintain free lists
        deleteFromFreeList(block);
        deleteFromFreeList(prev);
        deleteFromFreeList(next);
        
        // Update header of PREV so that size stretches encompass BLOCK and NEXT
        size += PAD_SIZE(PAYLOAD_SIZE(prev)) + PAD_SIZE(PAYLOAD_SIZE(next));
        PUT(HEADER(prev), PACK(size,FREE,IS_PREV_ALLOC(prev)));
        PUT(FOOTER(next), PACK(size,FREE,IS_PREV_ALLOC(prev)));
        
        addToFreeList(prev);
        return prev;
    }
}
/*
 * Takes a block and pushes it onto the front of the relevant free
 * list. Also sets the pointer to the start of the relevant free list
 * to this block.
 */
static void addToFreeList(void* block){
    size_class class = get_size_class(PAYLOAD_SIZE(block));
    void* head = FREE_LIST_NUM(class);
    
    // Set next pointer of BLOCK to the current free list head
    SET_NEXT_FREE_BLOCK(block,head);
    
    if (head != LIST_END)
        SET_PREV_FREE_BLOCK(head,block);
    
    // Head of a list should have the prev free block to point to list end
    SET_PREV_FREE_BLOCK(block, LIST_END);
    
    // Make the free list's new head BLOCK
    SET_FREE_LIST(class,block);
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
/*
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}
*/
/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
/*
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}
*/
/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    verbose = 1;

}
