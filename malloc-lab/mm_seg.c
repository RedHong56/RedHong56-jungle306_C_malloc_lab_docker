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
team_t team = { //이건 대학 과제라서
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

///////////////////// 가용리스트 조작 매크로 ////////////////////////////
/* Basic constants and macros */
// define : “컴파일 전에 이름 붙이기” 또는 “코드 치환 규칙 만들기”

// 기본 상수 사이즈 정의
#define WSIZE 4 // 워드 사이즈(헤더, 풋터의 크기)
#define DSIZE 8 // 더블 워드 사이즈(블록 최소 사이즈)
#define CHUNKSIZE (1<<12) // 초기 가용 블록과 힙 확장을 위한 기본 크기(페이지)

#define MAX(x,y) ((x)>(y) ? (x) : (y)) // 

// Macro 정의
#define PACK(size, alloc) ((size)|(alloc)) // PACK 매크로 : 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴 

/* 인자에 대하여 읽고 쓰기 */
#define GET(p) (*(unsigned int *)(p)) // GET 매크로 : 인자 p가 참조하는 워드를 읽어서 리턴  //(인자 p는 대개 void* 직접적으로 역참조할 수는 없다) 
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // PUT 매크로 : 인자 p가 가리키는 워드에 val을 저장

/* 헤더 또는풋터의 size와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 헤더와 풋터를 가리키는 포인터를 리턴 (bp = 블록 포인터) */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음 블럭과 이전 블럭을 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* PRED, SUCC 접근 매크로*/
#define PRED(bp) *(char**)(bp)
#define SUCC(bp) *(char**)(bp+DSIZE) 

//////////////////////segregated 선언/////////////////////////////


static void *seglist[10];

int find_index(int size)
{
    if (size<16)
    {   
        return 0;
    }
    else if (16<=size && size<32)
    {
        return 1;
    }
    else if (32<=size && size<64)
    {
        return 2;
    }
    else if (64<=size && size<128)
    {
        return 3;
    }
    else if (128<=size && size<256)
    {
        return 4;
    }
    else if (256<=size && size<512)
    {
        return 5;
    }
    else if (512<=size && size<1024)
    {
        return 6;
    }
    else if (1024<=size && size<2048)
    {
        return 7;
    }
    else if (2048<=size && size<4096)
    {
        return 8;
    }
    else // 4096 < size
    {
        return 9;
    }
}
//////////////////////////////////////////////////////////////
/* private global 변수 = static  */
static char *mem_heap; // 힙의 첫번째 바이트 포인터
static char *mem_brk; // 힙의 꼭대기 + 1
static char *mem_max_addr; // 합법적인 힙의 최대주소 +1
static char *heap_listp; // 저장용 포인터 변수 
////////////////////////mm_init///////////////////////////////////////
/* mm_init - initialize the malloc package. */
int mm_init(void)
{
    if (((heap_listp = mem_sbrk(4*WSIZE))) == (void *)-1) 
        return -1; 
    
    PUT(heap_listp, 0); //Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // Prologue pooter
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // Epilogue header
    heap_listp += (2*WSIZE);
    
    for(int i=0; i<10; i++){
        seglist[i] =NULL;
    }

    // last_bp = heap_listp;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
////////////////////////mm_malloc///////////////////////////////////////
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) //증가 되지 않으면 리턴 때리기
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{   
    for (int idx = find_index(asize); idx < 10; idx++)
    {
        void *cur = seglist[idx];
        while (cur != NULL)
        {
            if(GET_SIZE(HDRP(cur)) > asize)
                return cur;
            cur = SUCC(cur);
        }
    }
    return NULL;
} 

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    int idx = find_index(csize); // 블록의 사이즈
    delete_free_list(idx, bp);

    if ((csize - asize) >= (3*DSIZE)) // 할당하고 사이즈가 남을 때
    {
        idx = find_index(csize-asize);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *remain_bp = NEXT_BLKP(bp);
        PUT(HDRP(remain_bp), PACK(csize-asize, 0));
        PUT(FTRP(remain_bp), PACK(csize-asize, 0));
        insert_free_list(idx, remain_bp);
    }
    else 
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)
        return NULL;
    
    if(size <=  2* DSIZE)
        asize = 3 * DSIZE; // 4+8+8+4
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    //Search
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp,asize);
    return bp;
}
////////////////////////mm_free///////////////////////////////////////
/* mm_free - Freeing a block does nothing.*/
void mm_free(void *bp) //해제하려는 포인터
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
//////////////////////// coalesce  ///////////////////////////////////
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 가용 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 가용 상태
    size_t size = GET_SIZE(HDRP(bp));
    int idx;
    // CASE 1 : 양쪽 꽉 막힘
    if(prev_alloc && next_alloc){
        idx= find_index(GET_SIZE(HDRP(bp)));
        insert_free_list(idx, bp);
        return bp;
    }
    // CASE 2 : 뒤가 비었음
    else if(prev_alloc && !next_alloc){
        idx = find_index(GET_SIZE(HDRP(NEXT_BLKP(bp))));
        delete_free_list(idx, NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // CASE 3 : 앞이 비었음
    else if (!prev_alloc && next_alloc){
        idx = find_index(GET_SIZE(HDRP(PREV_BLKP(bp))));
        delete_free_list(idx, PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // CASE 4 : 양쪽 텅텅
    else{
        idx = find_index(GET_SIZE(HDRP(NEXT_BLKP(bp))));
        delete_free_list(idx, NEXT_BLKP(bp));
        idx = find_index(GET_SIZE(HDRP(PREV_BLKP(bp))));
        delete_free_list(idx, PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); // 양쪽 사이즈 더 해주고
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 왼쪽 메모리 블록의 헤더를 변경(왜냐? 그 블록의 헤더는 이제 합쳐진 하나의 블록의 헤더거든)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 오른쪽 메모리 블록의 푸터를 변경(왜냐? 그 블록의 푸터는 이제 합쳐진 하나의 블록의 푸터거든)
        bp = PREV_BLKP(bp);
    }

    idx = find_index(GET_SIZE(HDRP(bp)));
    insert_free_list(idx, bp);
    return bp;
}

////////////////////////mm_realloc///////////////////////////////////////
/* mm_realloc - Implemented simply in terms of mm_malloc and mm_free */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));   // 전체 블록 크기
    size_t copySize = oldsize - DSIZE;      // 헤더+풋터(DSIZE) 제외한 payload 크기

    if (size < copySize)
        copySize = size;

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
//////////////////////////segregated/////////////////////////////////////
void insert_free_list(int idx, void *bp)
{
    if (seglist[idx] == NULL){ // 헤드없을때
        seglist[idx] = bp;
        PRED(bp) = NULL;
        SUCC(bp) = NULL;
        return;
    }
    void *temp = seglist[idx];
    seglist[idx] = bp;
    PRED(bp) = NULL;
    SUCC(bp) = temp;
    PRED(temp) = bp;
}

void delete_free_list(int idx, void *bp)
{
    void *pred = PRED(bp);
    void *succ = SUCC(bp);
    // case 1 : bp가 헤드
    if (pred == NULL) {
        seglist[idx] = succ;          // 헤드를 다음 노드로 변경
        if (succ != NULL)
            PRED(succ) = NULL;        // 새 헤드의 pred는 NULL
    }
    // case 2 : bp가 헤드가 아닌 경우
    else {
        SUCC(pred) = succ;            // pred → succ 연결
        if (succ != NULL)
            PRED(succ) = pred;        // succ ← pred 연결
    }
}
