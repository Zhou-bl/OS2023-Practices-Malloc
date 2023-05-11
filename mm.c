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
#define PACK(size, prealloc,alloc) ((size) | (PREALLOC(prealloc)) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREALLOC(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//Explicit free list:
/*
#define GET_PREV(p) (*(unsigned int *)(p))
#define SET_PREV(p, prev) (*(unsigned int *)(p) = (prev))
#define GET_NEXT(p) (*((unsigned int *)(p)+1))
#define SET_NEXT(p, val) (*((unsigned int *)(p)+1) = (val))
*/

#define READ(p)       (*(unsigned int *)(p))
#define WRITE(p, val) (*(unsigned int *)(p) = (val))

#define GET_PREV(bp) (READ((char *)(bp))         == 0? NULL : (int *)((long)(READ((char *)(bp)))         + (long)(heap_listp)))
#define GET_NEXT(bp) (READ((char *)(bp) + WSIZE) == 0? NULL : (int *)((long)(READ((char *)(bp) + WSIZE)) + (long)(heap_listp)))
#define SET_PREV(bp, val) WRITE((char *)(bp),         (val) == 0? 0 : ((long)val - (long)(heap_listp)))
#define SET_NEXT(bp, val) WRITE((char *)(bp) + WSIZE, (val) == 0? 0 : ((long)val - (long)(heap_listp)))

//remove the footer of the allocated block:
#define PREALLOC(x) ((!x) ? 0 : 2)

//Use some strange mathod to change the strategy: 选取前 FIRST_FIT_NUM 个空闲块中最小的一个:
#define FIRST_FIT_NUM 7

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
inline void set_next_prealloc(void *bp, size_t prealloc);

inline void set_next_prealloc(void *bp, size_t prealloc){
    size_t size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(size,prealloc,alloc));
}

static void remove_from_free_list(void *bp){
    //被分配了或者空指针直接返回：
    if(bp == NULL || GET_ALLOC(HDRP(bp)) == 1){
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
    //mm_checkheap(2);
}

static void insert_to_free_list(void *bp){
    if(bp == NULL) return;
    //如果列表是空的，直接插入
    if(free_list_head == NULL){
        //printf("insert to empty list\n");
        free_list_head = bp;
        SET_NEXT(bp, 0);
        SET_PREV(bp, 0);
    }
    else {
        //插到头部：
        //printf("insert to head\n");
        //printf("bp: %p\n", bp);
        //printf("free_list_head: %p\n", free_list_head);
        //printf("NEXT %p\n", ((unsigned int *)(bp)+1));
        //unsigned int tt = free_list_head;
        //SET_PREV(bp, 0);
        SET_NEXT(bp, free_list_head);
        //void *tmp = GET_NEXT(bp);
        //printf("NEXT free pointer: %p\n", tmp);
        SET_PREV(free_list_head, bp);
        //tmp = 
        free_list_head = bp;
        SET_PREV(bp, 0);
    }
    //mm_checkheap(2);
    return;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t prealloc;
    words = (words & 1) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(words)) == -1) return NULL;
    //printf("extend heap: %p\n", bp);
    //将原来尾块的头部（尾块只有头部）替换为新的空闲块的头部，新的空闲块的大小为words，然后设定新的尾块以及新的空闲块的尾部
    //memset(bp, 0, words);
    prealloc = GET_PREALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(words, prealloc, 0)); //free block header
    //printf("1\n");
    PUT(FTRP(bp), PACK(words, prealloc, 0)); //free block footer
    //printf("2\n");
    SET_PREV(bp, 0); SET_NEXT(bp, 0); //先不插入空闲链表
    //printf("3\n");
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1)); //new epilogue header
    //printf("4\n");
    return coalesce(bp);
}

static void* coalesce(void *bp)
{
    //printf("There is something  wrong in this function!\n");
    //void* prev_bp = PREV_BLKP(bp);
    void* next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_PREALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    //printf("Get here!\n");
    //printf("prev_alloc: %d, next_alloc: %d\n", prev_alloc, next_alloc);

    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && next_alloc){
        insert_to_free_list(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        remove_from_free_list(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 1, 0));
        PUT(FTRP(bp), PACK(size, 1, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        void *prev_bp = PREV_BLKP(bp);
        remove_from_free_list(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        PUT(FTRP(bp), PACK(size, GET_PREALLOC(HDRP(prev_bp)),0));
        PUT(HDRP(prev_bp), PACK(size, GET_PREALLOC(HDRP(prev_bp)), 0));

        bp = prev_bp;
    }
    else
    {
        void *prev_bp = PREV_BLKP(bp);
        remove_from_free_list(prev_bp);
        remove_from_free_list(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(FTRP(next_bp));
        PUT(HDRP(prev_bp), PACK(size, GET_PREALLOC(HDRP(prev_bp)),0));
        PUT(FTRP(next_bp), PACK(size, GET_PREALLOC(HDRP(prev_bp)), 0));

        bp = prev_bp;
    }
    set_next_prealloc(bp, 0);
    insert_to_free_list(bp);
    return bp;
}


static void *find_fit_in_list(size_t asize){
    //mm_checkheap(1);
    for(void *bp = free_list_head; bp != NULL; bp = GET_NEXT(bp)){
        //printf("heap_listp: %p\n", heap_listp);
        //printf("heap_bound: %p\n", heap_listp + mem_heapsize());
        //printf("bp: %p\n", bp);
        if(GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
    return NULL;
}

static void *find_num_fit_in_list(size_t asize){
    size_t cur_num = 0, cur_size = -1;
    void *res_bp = NULL;
    for(void *bp = free_list_head; bp != NULL && cur_num < FIRST_FIT_NUM; bp = GET_NEXT(bp)){
        if(GET_SIZE(HDRP(bp)) >= asize){
            cur_num++;
            if(!res_bp){
                res_bp = bp;
                cur_size = GET_SIZE(HDRP(bp));
            } else if(GET_SIZE(HDRP(bp)) < cur_size){
                res_bp = bp;
                cur_size = GET_SIZE(HDRP(bp));
            }
        }
    }
    return res_bp;
}

static void *find_fit(size_t asize){
    //return find_fit_in_list(asize); 
    return find_num_fit_in_list(asize);
}

static void place(void* bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));
    remove_from_free_list(bp);

    if ((size - asize) >= MINBLOCKSIZE) // split block
    {
        PUT(HDRP(bp), PACK(asize, GET_PREALLOC(HDRP(bp)), 1));
        //PUT(FTRP(bp), PACK(asize, GET_PREALLOC(HDRP(bp)), 1));
        //void* new_bp = ;
        PUT(HDRP(NEXT_BLKP(bp)), PACK(size - asize, 1, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size - asize, 1, 0));
        //set_next_prealloc(bp, 1);
        SET_PREV(NEXT_BLKP(bp), 0);
        SET_NEXT(NEXT_BLKP(bp), 0);
        coalesce(NEXT_BLKP(bp));
    }
    else // do not split
    {
        PUT(HDRP(bp), PACK(size, GET_PREALLOC(HDRP(bp)), 1));
        //PUT(FTRP(bp), PACK(size, 1));
        set_next_prealloc(bp, 1);
    }
}

int mm_init(void){
    //printf("mm_init\n");
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) return -1;
    //printf("Finish heap init\n");
    PUT(heap_listp, 0); /*Alignment padding*/
    //序言块:头部+尾部(序言块的状态是被占用的, 大小为两字节（头部和尾部各一个字节）)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));
    heap_listp += DSIZE; //指向序言块的尾部
    free_list_head = NULL;
    //printf("Finish heap init\n");

#ifdef NEXT_FIT
    recover = heap_listp;
#endif

    //扩展堆
    //if(extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;
    //printf("[End] mm_init\n");
    //mm_checkheap(1);
    return 0;
}
size_t malloc_cnt = 0;
void *malloc(size_t size){
    //printf("malloc %ld\n", size);
    size_t adjust_size, extend_size;
    char *bp;
    //忽略无效请求
    if(size == 0) return NULL;
    //调整块大小
    adjust_size = MAX(MINBLOCKSIZE, DSIZE * ((size + WSIZE + DSIZE - 1) / DSIZE));
    //搜索空闲链表
    //printf("Start search!\n");
    if((bp = find_fit(adjust_size)) != NULL){
        
        //printf("hhh find!\n");
        place(bp, adjust_size);
        //mm_checkheap(1);
        //mm_checkheap(2);
        return bp;
    }
    //没有找到合适的空闲块，扩展堆
    //extend_size = MAX(adjust_size, CHUNKSIZE);
    extend_size = adjust_size;
    if((bp = extend_heap(extend_size / WSIZE)) == NULL) return NULL;
    //printf("hhh extend!\n");
    place(bp, adjust_size);
    //mm_checkheap(2);
    return bp;
}

void free(void *ptr){
    //ptr为空指针，直接返回
    //printf("free %p\n", ptr);
    if(ptr == NULL) return;
    size_t size = GET_SIZE(HDRP(ptr));
    size_t prealloc = GET_PREALLOC(HDRP(ptr));
    //改变头部和尾部的状态位
    if (heap_listp == 0){
        //printf("?????????????????????\n");
        mm_init();
    }
    PUT(HDRP(ptr), PACK(size, prealloc, 0));
    PUT(FTRP(ptr), PACK(size, prealloc, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0, GET_ALLOC(HDRP(NEXT_BLKP(ptr)))));
    if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))))PUT(FTRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0, GET_ALLOC(HDRP(NEXT_BLKP(ptr)))));
    SET_PREV(ptr, 0); SET_NEXT(ptr, 0);
    coalesce(ptr);
    //mm_checkheap(2);
}

/*
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    prev_listp = coalesce(ptr);
}
*/

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
    verbose = verbose;
    /*Get gcc to be quiet. */
    printf("mm_checkheap\n");
    if(verbose == 1){
        /*
        printf("[Start] mm_checkheap=========================================================================\n");
        for(void *bp = free_list_head; bp != NULL; bp = GET_NEXT(bp)){
            printf("%p\t", bp);
            printf("size:%d\t", GET_SIZE(HDRP(bp)));
            printf("prev:%p\t", GET_PREV(bp));
            printf("next:%p\n", GET_NEXT(bp));
        }
        printf("\n");
        printf("[End] mm_checkheap=========================================================================\n");
        */
    }
    if(verbose == 2){

        printf("[Start] Check heap========================================================================\n");
        for(void *bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            printf("%p\t\t", bp);
            printf("size:%d\t\t", GET_SIZE(HDRP(bp)));
            printf("alloc:%d\n", GET_ALLOC(HDRP(bp)));
            //printf("prev:%p\t", GET_PREV(bp));
            //printf("next:%p\n", GET_NEXT(bp));
        }
        printf("[End] Check heap========================================================================\n");

        //check linked list:
        printf("[Start] Check linked list======================================================================\n");
        printf("heap_listp:%p\n", heap_listp);
        printf("heap_bound:%p\n", heap_listp + mem_heapsize());
        for(void *bp = free_list_head; bp != NULL; bp = GET_NEXT(bp)){
            printf("%p\t", bp);
            printf("size:%d\t", GET_SIZE(HDRP(bp)));
            printf("prev:%p\t", GET_PREV(bp));
            printf("next:%p\n", GET_NEXT(bp));
        }
        printf("[End] Check linked list========================================================================\n");
        printf("\n\n");
    }
    
}