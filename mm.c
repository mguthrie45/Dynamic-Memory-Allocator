/*
 * mm.c
 *
 * Name: Max Guthrie, Harel Tillinger
 * 
 * This project creates a memory allocator using a segregated free list implementation. The overhead is 48 bytes for each block.
 * All blocks are 16-byte aligned and contain header and footer.
 * The project recreates 4 main functions (along with many helper functions): malloc, calloc, free, and realloc.
 *  
 * We went about different ways to reduce fragmentation those of which were: splitting blocks (split_block helper) and bidrectional coalescing.
 * 
 * Segregated List Layout: We designated 16 classes and held pointers to each free list in an array. A mapping function (map_to_class) was used to determine the correct
 * class for a block. Each free list contains blocks within their respective size ranges to enhance throughput when finding fits.
 * 
 * Allocated Blocks:
 * If a block is found that is able to fit the aligned allocation size, two of the following could occur. One, there is a perfect fit which would simply require the 
 * free bit. Two, the block would require splitting to reduce waste space and the unused space would be reserved and put in the free list. Otherwise, if no fit was found,
 * extra space for the heap was requested using mem_sbrk. 
 * 
 * Freeing Blocks:
 * When freeing a block, there are two possiblities. The first being no coalescing needs to occur (no free blocks next to it). The second is that there exists one or two
 * free blocks next to it. In the first case, the block can simply be set free and added to the free list of correct class. In the second case, the joined blocks will be 
 * deleted from the free list and the block of combined size will be inserted.
 * 
 *   
 * 
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* The number of classes for seglist */
#define MINCLASSSIZE 48
#define SHIFT 5
#define CLASSNUM 16
#define CHUNKSIZE 2048

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static int log2Floor(size_t s) {
    return(sizeof(size_t) * 8 -1) ^ __builtin_clzl(s);
}

static size_t max(size_t s1, size_t s2) {
    return s1 >= s2 ? s1 : s2;
}

typedef struct header {
    size_t size;
    bool freed;
    struct header *next;
    struct header *prev;
} header;

typedef struct footer {
    size_t size;
    bool freed;
} footer;

size_t HSIZE = sizeof(header);
size_t FSIZE = sizeof(footer);

//an array of free list pointers for each class
header* flp_list[CLASSNUM];

//The number of blocks in FL
int frees = 0;
int mallocs = 0;
int extends = 0;

header *heap = NULL; //points to first block in heap
void *end = NULL; //points to boundary of heap
void *heap_brk = NULL; //points to last created block in heap.


//maps the size to the correct class using log2
static int map_to_class(size_t size) {
    int class = log2Floor(size);
    int actual = class - SHIFT;
    return actual > CLASSNUM-1 ? CLASSNUM-1 : actual;
}

//sets all free list pointers initially to NULL.
static void init_classes() {
    for (int i = 0; i < CLASSNUM; i++) {
    	flp_list[i] = NULL;
    }
}

/*Given the header of a block, returns a pointer to the block(alloc or free) before it.*/
static header *prev_blk(header *block) {
    //check if there even exists a previous block
    footer *prev_footer = (void*)block - FSIZE;
    if ((void*)prev_footer < (void*)heap)
    	return NULL;
    return (void*)block - prev_footer -> size;
}

/*Given the header of a block, returns a pointer to the block(alloc or free) after it.*/
static header *next_blk(header *block) {
    if (block == NULL) return NULL;
    header *next_header = (void*)block + block -> size;
    if ((void*)next_header >= end)
    	return NULL;
    return (void*)block + block -> size;
}

/*Given the header of a block, returns a pointer to the block's footer.*/
static footer *get_footer(header *block) {
    return (void*)block + block -> size - FSIZE;
}

/*Given the footer of a block, returns a pointer to the block's header.*/
static header *get_header(footer *block) {
    return (void*)block - block -> size + FSIZE;
}

/* used for malloc: takes in a size and returns the necessary and aligned allocation size. */
static size_t alloc_size(size_t size) {
    return align(size + HSIZE + FSIZE);
}

//Finds the number of blocks in a given class
int get_count(int class) {
    header *curr = flp_list[class];
    int ct = 0;
    while (curr != NULL) {
    	ct += 1;
        curr = curr -> next;
    }
    return ct;
}

/* Given the block, it will be deleted from the appropriate class's free list.
Warning: Do not change size of block then delete it. The block must be deleted in its original size. */
static void del_fl_seg(header *block, size_t size) {
    frees -= 1;
    int class = map_to_class(block->size);
    
    header *prev = block -> prev;
    header *next = block -> next;
    
    block -> prev = NULL;
    block -> next = NULL;
    
    //if the block isn't the first in the free list, change prev's pointer.
    if (prev == NULL) {
    	flp_list[class] = next;
    }
    //otherwise, flp must change to the next free block
    else 
    	prev -> next = next;
    //if the block isn't the last free block in the list, the next's prev pointer must change.
    if (next != NULL)
    	next -> prev = prev;
}

/* Given a block, it will be added to the appropriate free list class when freed.
Must set freed bit to true beforehand. */
static void add_fl_seg(header *block, size_t size) {
    frees += 1;
    int class = map_to_class(size);
    
    header *prev_head = flp_list[class];
    
    //add to head of the free list.
    
    block -> prev = NULL;
    block -> next = prev_head;
    flp_list[class] = block;
    //add to head of the free list.
    
    if (prev_head != NULL)
        prev_head -> prev = block;
}

/* Given a block and the value to set, it will change the header and footer accordingly.
Warning: If the block's size has changed, make sure to change the size prior to calling so that this function
can properly locate the footer. */
static void set_free(header *block, bool freed) {
    footer *foot = get_footer(block);
    block -> freed = freed;
    foot -> freed = freed;
}

/* Given a block and the size value, it will change the header and footer accordingly. */
static void set_size(header *block, size_t size) {
    block -> size = size;
    footer *foot = get_footer(block);
    foot -> size = size;
}
 
 
 /*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    init_classes();
    frees = 0;
    mallocs = 0;
    extends = 0;
    end = NULL;
    heap_brk = NULL;
    
    //intialized 4K block.
    size_t init_size = alloc_size(CHUNKSIZE);
    
    heap_brk = mem_sbrk(init_size);
    end = heap_brk + init_size;
    
    //if memory can't be allocated, return failure
    if (*(char*)heap_brk == -1) {
    	return false;
    }
    
    //initialize the first block in heap
    heap = (void*) heap_brk;
    set_size(heap, init_size);
    set_free(heap, true);
    heap -> next = NULL;
    heap -> prev = NULL;
    
    //add the first block to the FL.
    add_fl_seg(heap, init_size);
    
    return true;
}

/* Given an aligned size, searches at the starting class and goes through all
free blocks (including classes above starting) until a block is found. If no block
can be found, NULL is returned. */
static header *find_fit_seg(size_t asize) {
    //fit wont be in any class under
    int starting_class = map_to_class(asize);
    for (int class = starting_class; class < CLASSNUM; class++) {
    	header *curr_block = flp_list[class];
    	if (curr_block == NULL)
    	    continue;
    	    
    	//search the class's free list until a block is found or the end is reached.
    	while (curr_block != NULL) {
    	    if (curr_block -> size >= asize)
    	    	return curr_block;
    	    curr_block = curr_block -> next;
    	}
    }
    return NULL;
}

/* If a fit causes internal fragmentation, this will split the block into two.
1) the left block will be allocated to the size len.
2) The right block will be freed with the remaining size.

If the remaining size isn't enough to hold a payload, however, no splitting will occur. */
void split_block(header *free_block, size_t len) {
    size_t new_size = len;
    size_t old_size = free_block -> size;
    size_t size_remain = old_size - new_size;
    
    //if remaining size is nonzero but can't fit a header/footer, it's useless
    if (size_remain < HSIZE+FSIZE) {
        del_fl_seg(free_block, old_size);
    	set_free(free_block, false);
    	return;
    }
    
    //otherwise, delete free_block from fl and change its size.
    del_fl_seg(free_block, old_size);
    set_size(free_block, new_size);
    set_free(free_block, false);
    
    //create new block (right) and change its size, and add to free list.
    header *new_block = next_blk(free_block);
    set_size(new_block, size_remain);
    set_free(new_block, true);
    add_fl_seg(new_block, size_remain);
}

/*This function coalesces (if necessary) when freeing a block
Handles all 4 cases:
1) Left + Middle
2) Middle + right
3) Left + Middle + right
4) None
*/
static header *coalesce(header *free_block) {
    header *prev_block = prev_blk(free_block);
    header *next_block = next_blk(free_block);
    
    //Looks to see if the previous and next blocks are free
    bool prev_free = prev_block != NULL && prev_block -> freed;
    bool next_free = next_block != NULL && next_block -> freed;
    
    size_t new_size;
    //If they both are occupied, then add the free block
    if (!prev_free && !next_free){
    	new_size = free_block -> size;
    }
    //If the left is free and the right is not free, then coalesce and join into previous block. Map it to the correct class and insert into free list.
    else if (prev_free && !next_free) {
        new_size = prev_block -> size + free_block -> size;
        del_fl_seg(prev_block, prev_block -> size);
        free_block = prev_block;
        set_size(free_block, new_size);
        set_free(free_block, true);
        
    }
    //If the left is not free and the right is free, then coalesce and join into free block. Map it to the correct class and insert into free list.
    else if (!prev_free && next_free){
        new_size = free_block -> size + next_block -> size;
        del_fl_seg(next_block, next_block -> size);
        set_size(free_block, new_size);
        set_free(free_block, true);
    }
    //If the all the blocks are free, then coalesce all three and place it in the correct class
    else{
        new_size = prev_block -> size + free_block -> size + next_block -> size;
        del_fl_seg(next_block, next_block -> size);
        free_block = prev_block;
        del_fl_seg(free_block, prev_block -> size);
        set_size(free_block, new_size);
        set_free(free_block, true);
    }
    add_fl_seg(free_block, new_size);
    return free_block;
}


/* If no blocks can fit a new payload, more heap space will be requested. The extend
size will take into account if the last block is free. If it isn't,
it will be the maximum of the requested size and the CHUNKSIZE. */
static header *extend_heap(size_t size) {
    extends++;
    void *block;
    
    //if mem_sbrk can't give more space, then return failure.
    if ((long)(block = mem_sbrk(size)) == -1) {
    	return NULL;
    }
    
    heap_brk = block;
    header *hblock = (header*)block;
    
    set_size(hblock, size);
    set_free(hblock, true);
    end = block + size;
    
    //coalesce so that if the last block is free, join it
    return coalesce(hblock);
}

/*
 * malloc: Given the payload size, a fit found in the free list and allocated.
 If no fit can be found, the heap will need to be extended. A pointer to the payload
 will be returned on success, and NULL will be returned on failure.
 
 Case 1) Fit is perfect (aligned size == free_block's size): return pointer to that payload
 Case 2) Fit needs split (aligned size is less): blocks are split and pointer to payload returned
 Case 3) No fit is found: heap must be extended using extend_heap. Return payload pointer after heap_brk.
 Case 4) size is 0: return NULL
 */
void* malloc(size_t size)
{
    mallocs++;
    if (size == 0) {
    	return NULL;
    }
    
    void *mem;
    size_t actual_size = alloc_size(size);
    
    //find a fit in the free list
    header *fit_block = find_fit_seg(actual_size);
    bool found = fit_block != NULL;
    
    //If the allocated size is less than the fit's size, the block must be split.
    if (found) {
    	split_block(fit_block, actual_size);
    	mem = (void*)++fit_block;
    	return mem;
    }
    //If no block has been found, the heap needs extension
    else {
        size_t extend_size;
        header *last_block = prev_blk(end);
        
        if (last_block -> freed) {
            extend_size = actual_size - last_block -> size;
        }
        else {
            extend_size = max(actual_size, CHUNKSIZE);
        }
        
        header *new_block = extend_heap(extend_size);
    	//if heap can't be extended, then return NULL
    	if (new_block == NULL) {
    	    return NULL;
    	}
    	
    	//If extend_size is larger than necessary, split the block
    	split_block(new_block, actual_size);
    	mem = (void*)++new_block;
    	return mem;
    }
    return NULL;
}

//Uses get_count() and finds the number of total blocks in FL
int get_FL_count() {
    int ct = 0;
    for (int class = 0; class < CLASSNUM; class++) {
        ct += get_count(class);
    }
    return ct;
}

/*
 * free
 */
//Frees the block
void free(void* ptr)
{   
    //gets block size by subtracting the pointer from header size
    header *block = ptr - HSIZE;   

    if (ptr == NULL){
        return;
    }
    
    //Call Coalesce and free block
    set_free(block, true);
    coalesce(block);
}

/*
 * realloc: Given the payload pointer and the new allocation size,
 a pointer is returned to the available (new/original) payload on success,
 and NULL is returned on failure.
 */
void* realloc(void* oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    void *newptr;
    size_t newsize;
    size_t oldsize;
    
    //If size is negative (illegal), then return NULL
    if ((int)(size) < 0)
        return NULL;
	
    //if size is zero, then just free that pointer
    if (size == 0){
        free(oldptr);
        return NULL;
    }
    
    //if the pointer is NULL, then allocate for the new size
    if (oldptr == NULL){
        newptr = malloc(size);
        return newptr;
    }
    
    header *old_block = oldptr - HSIZE;
    oldsize = old_block -> size;
    newsize = alloc_size(size);
    
    if (newsize == oldsize) {
        return oldptr;
    }
    
    //if size is smaller than block's size, free the larger block and allocate into a smaller block
    else if (newsize < oldsize) {
        newptr = malloc(size);
        if (newptr == NULL) {
            return NULL;
        }
        
        memcpy(newptr, oldptr, newsize-HSIZE-FSIZE);
        free(oldptr);
        return newptr;
    }
    
    //if the new size is larger, then a new block needs to be found, and the old block can be freed.
    else {
    	//allocate the new size, but if it fails, then return NULL
        newptr = malloc(size);
        if (newptr == NULL) {
            return NULL;
        }
        
        //must copy over the payload from the old payload to avoid garbling
        size_t payload_size = oldsize - HSIZE - FSIZE;
        memcpy(newptr, oldptr, payload_size);
        
        //the old block is no longer in use, so it can be freed
        free(oldptr);
        return newptr;
    }
    return NULL;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}
//Checks if the block is free
static bool check_free_block(header *block) {
    return block -> freed;
}
//Put in the class number, and make sure that it is in the correct class
static bool correct_class(header *block, int curr_class) {
    int class = map_to_class(block -> size);
    return curr_class == class;
}
//Make sure that the header and footer have the same info
static bool hf_consistency(header *block) {
    if (block == NULL) return false;
    footer *block_foot = get_footer(block);
    if (block_foot == NULL) return false;
    return block -> size == block_foot -> size 
    && block -> freed == block_foot -> freed;
}
//Ensure that the blocks have been coalesced correctly
static bool correct_coal(header *block) {
    if (!block -> freed) {
        return true;
    }
    header *prev = prev_blk(block);
    header *next = next_blk(block);
    
    if (prev != NULL && prev -> freed) {
        return false;
    }
    if (next != NULL && next -> freed) {
        return false;
    }
    return true;
}



/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {	
    //checks if the number of free blocks equal the number of blocks in FL
    if (frees != get_FL_count()) {
    	dbg_printf("ERROR: the free list fails to capture all free blocks.\n");
    	return false;
    }
    
    //loop through seg list to check freeness, correct class mapping, and correct coalescing (through helper functions)

    for (int class=0; class < CLASSNUM; class++){
        header *curr = flp_list[class];
        int ct = 0;
        while (curr != NULL){
        ct += 1;
            if (!check_free_block(curr)){
                printf("ERROR: block at %p shouldn't be in free list .\n", curr);
                dbg_printf("ERROR: block at %p shouldn't be in free list .\n", curr);
                return false;
            }
            if (!correct_class(curr,class)){
                dbg_printf("ERROR: block at %p is clas %i but should be class %i\n", curr, class, map_to_class(curr->size));
                printf("ERROR: block at %p is clas %i but should be class %i\n", curr, class, map_to_class(curr->size));
                return false;
            }
            if (!hf_consistency(curr)){
                dbg_printf("ERROR: header and footer do not match in block at %p\n", curr);   
                printf("ERROR: header and footer do not match in block at %p\n", curr); 
                return false;
            }
            curr = curr -> next;
        }
            
    }
    //loop through entire heap to check valid addresses, valid alignment, and header/footer consistency (through the use of helper functions)
    header *current = heap;
    while (current != NULL && (void*)(current) < end){
        if (!in_heap(current)){
            dbg_printf("ERROR: block at %p is not in heap(%p: %p)\n", current, mem_heap_lo, mem_heap_hi);
            printf("ERROR: block at %p is not in heap(%p: %p)\n", current, mem_heap_lo, mem_heap_hi);
            return false;
        }
        if (!aligned(current)){
            dbg_printf("ERROR: block at %p not aligned by %i\n", current, ALIGNMENT);
            printf("ERROR: block at %p not aligned by %i\n", current, ALIGNMENT);
            return false;
        }
        if (!correct_coal(current)){
            dbg_printf("ERROR: block at %p has free blocks next to it has have not been coalesced.\n", current);
            printf("ERROR: block at %p has free blocks next to it has have not been coalesced.\n", current);
            return false;
        }
        current = next_blk(current);
    }
    return true;
}

