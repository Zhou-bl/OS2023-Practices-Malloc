#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define BSIZE 16
#define MINBLOCKSIZE 16
#define CHUNKSIZE (1<<10) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//Explicit free list:
#define GET_PREV(p) (*(unsigned int *)(p))
#define SET_PREV(p, prev) (*(unsigned int *)(p) = (prev))
#define GET_NEXT(p) (*((unsigned int *)(p)+1))
#define SET_NEXT(p, val) (*((unsigned int *)(p)+1) = (val))

//#define NEXT_FIT

#ifdef NEXT_FIT
static char *recover;
#endif


/*
 * mm_init - Called when a new trace starts.
 */
static char *heap_listp = 0;
static char *free_list_head = 0;

//Some tool functions:

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void remove_from_free_list(void *bp){
    //被分配了或者空指针直接返回：
    if(bp == NULL || GET_ALLOC(HDRP(bp))){
        return;
    }
    void *prev, *next;
    prev = GET_PREV(bp); next = GET_NEXT(bp);
    SET_PREV(bp, 0); SET_NEXT(bp, 0);//消除前驱后继
    if(prev == NULL && next == NULL){
        free_list_head = NULL;
    }
    else if(prev == NULL && next != NULL){
        //next 成为第一个空节点:
        SET_PREV(next, 0);
        free_list_head = next;
    }
    else if(prev != NULL && next == NULL){
        SET_NEXT(prev, 0);
    }
    else {
        SET_NEXT(prev, next);
        SET_PREV(next, prev);
    }
}

static void insert_to_free_list(void *bp){
    if(bp == NULL) return;
    //如果列表是空的，直接插入
    if(free_list_head == NULL){
        free_list_head = bp;
    }
    else {
        //插到头部：
        SET_NEXT(bp, free_list_head);
        SET_PREV(free_list_head, bp);
        free_list_head = bp;
    }
    return;
}

static void *extend_heap(size_t words){
    char *bp;
    words = (words & 1) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(words)) == -1) return NULL;
    //将原来尾块的头部（尾块只有头部）替换为新的空闲块的头部，新的空闲块的大小为words，然后设定新的尾块以及新的空闲块的尾部
    PUT(HDRP(bp), PACK(words, 0)); //free block header
    PUT(FTRP(bp), PACK(words, 0)); //free block footer
    SET_PREV(bp, 0); SET_NEXT(bp, 0); //不插入空闲链表
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //new epilogue header
    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //1.如果前后块都已经分配，则直接返回
    if(prev_alloc && next_alloc){
        //printf("[End] coalesce\n");
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        remove_from_free_list(PREV_BLKP(bp));
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
#ifdef NEXT_FIT
    if((recover > (char *)bp) && (recover < NEXT_BLKP(bp))){
        recover = bp;
    }
#endif
    insert_to_free_list(bp);
    return bp;

}

static void *find_fit_in_list(size_t asize){
    for(void *bp = free_list_head; bp != 0; bp = GET_NEXT(bp)){
        if(GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
    return NULL;
}

static void *find_fit(size_t asize){
    void *bp = find_fit_in_list(asize);
    if(bp != NULL) return bp;
    else {
        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
        return NULL;
    }
#ifdef NEXT_FIT
    char *oldrecover = recover;
    //Search from the recover pointer:
    for(; GET_SIZE(HDRP(recover)) > 0; recover = NEXT_BLKP(recover)){
        if(!GET_ALLOC(HDRP(recover)) && (asize <= GET_SIZE(HDRP(recover))))
            return recover;
    }
    //Search from the start of the list:
    for(recover = heap_listp; recover < oldrecover; recover = NEXT_BLKP(recover)){
        if(!GET_ALLOC(HDRP(recover)) && (asize <= GET_SIZE(HDRP(recover))))
            return recover;
    }
    return NULL;
#endif

    
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    remove_from_free_list(bp);

    if((csize - asize) >= MINBLOCKSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        SET_PREV(bp, 0); SET_NEXT(bp, 0);
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

int mm_init(void){
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) return -1;
    PUT(heap_listp, 0); /*Alignment padding*/
    //序言块:头部+尾部(序言块的状态是被占用的, 大小为两字节（头部和尾部各一个字节）)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE); //指向序言块的尾部
    free_list_head = NULL;

#ifdef NEXT_FIT
    recover = heap_listp;
#endif

    //扩展堆
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;
    return 0;
}

void *malloc(size_t size){
    size_t adjust_size, extend_size;
    char *bp;
    //忽略无效请求
    if(size == 0) return NULL;
    //调整块大小
    if(size <= DSIZE) adjust_size = 2 * DSIZE;
    else adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    //搜索空闲链表
    if((bp = find_fit(adjust_size)) != NULL){
        place(bp, adjust_size);
        //printf("[End] malloc_cnt = %d\n", malloc_cnt);
        return bp;
    }
    //没有找到合适的空闲块，扩展堆
    extend_size = MAX(adjust_size, CHUNKSIZE);
    if((bp = extend_heap(extend_size / WSIZE)) == NULL) return NULL;
    place(bp, adjust_size);
    return bp;
}

void free(void *ptr){
    //ptr为空指针，直接返回
    if(ptr == 0) return;
    size_t size = GET_SIZE(HDRP(ptr));
    //改变头部和尾部的状态位
    if (heap_listp == 0){
        mm_init();
    }
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    SET_PREV(ptr, 0); SET_NEXT(ptr, 0);
    coalesce(ptr);
}

void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    if(size == 0) {
        free(ptr);
        return 0;
    }
    if(ptr == NULL) {
        return malloc(size);
    }
    newptr = malloc(size);
    if(!newptr) {
        return 0;
    }
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    /* Free the old block. */
    free(ptr);
    return newptr;
}
void *calloc (size_t nmemb, size_t size){
    //printf("[Start] Calloc\n");
    size_t total_size = nmemb * size;
    void *newptr = malloc(total_size);
    memset(newptr, 0, total_size);
    return newptr;
}
void mm_checkheap(int verbose){
    /*Get gcc to be quiet. */
    verbose = verbose;
}