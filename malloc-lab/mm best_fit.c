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
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0xf)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

///////////////////// 가용리스트 조작 매크로 ////////////////////////////
/* Basic constants and macros */
// define : “컴파일 전에 이름 붙이기” 또는 “코드 치환 규칙 만들기”

// 기본 상수 사이즈 정의
#define WSIZE 8 // 워드 사이즈(헤더, 풋터의 크기)
#define DSIZE 16 // 더블 워드 사이즈(블록 최소 사이즈)
#define CHUNKSIZE (1<<12) // 초기 가용 블록과 힙 확장을 위한 기본 크기(페이지)

#define MAX(x,y) ((x)>(y) ? (x) : (y)) // 

// Macro 정의
#define PACK(size, alloc) ((size)|(alloc)) // PACK 매크로 : 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴 

/* 인자에 대하여 읽고 쓰기 */
#define GET(p) (*(unsigned long *)(p)) // GET 매크로 : 인자 p가 참조하는 워드를 읽어서 리턴  //(인자 p는 대개 void* 직접적으로 역참조할 수는 없다) 
#define PUT(p, val) (*(unsigned long *)(p) = (val)) // PUT 매크로 : 인자 p가 가리키는 워드에 val을 저장

/* 헤더 또는풋터의 size와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0xf)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 헤더와 풋터를 가리키는 포인터를 리턴 (bp = 블록 포인터) */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음 블럭과 이전 블럭을 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//////////////////////////////////////////////////////////////
/* private global 변수 = static  */
static char *mem_heap; // 힙의 첫번째 바이트 포인터
static char *mem_brk; // 힙의 꼭대기 + 1
static char *mem_max_addr; // 합법적인 힙의 최대주소 +1
static char *heap_listp; // 저장용 포인터 변수 

static void *last_bp = NULL; // 이 포인터는 “지난번 malloc이 어디서 블록을 찾고 멈췄는가”를 저장하는 역할.
////////////////////////extent_heap///////////////////////////////////
static void *extend_heap(size_t words)
{
    char *bp; //블럭 포인터
    size_t size;

    /* Allocate an even numer of words to maintain aligment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀 짝 확인후 짝 만들어 정렬

    if((long)(bp = mem_sbrk(size)) == -1) // 힙 확장에 실패했을 때
        return NULL;

    /* Initialize free block header/footer and the epiloogue header */
    PUT(HDRP(bp), PACK(size, 0)); // 가용 블록 header
    PUT(FTRP(bp), PACK(size, 0)); // 가용 블록 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 header

    /* Coalesce if the previous block was free */
    return coalesce(bp); // 이전 블록이 free이면 병합(x)
                         // 양 옆을 확인해서 free된 블록이면 병합 아님 그냥 둠
}

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
    
    last_bp = heap_listp;
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


static void *find_fit(size_t asize)
{   
    void *cur_bp = last_bp;
    // next-fit은 탐색 방향과 시작점만 기억

    // 더 이상 heap의 맨 처음부터 탐색하지 않는다.
    // 기억된 포인터 위치에서부터 다음 블록으로 쭉 훑기 시작한다.
    
    for (last_bp; GET_SIZE(HDRP(last_bp)) > 0; last_bp = NEXT_BLKP(last_bp)) 
        {
            if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp))))  // 적합한 free 블록을 찾는 순간,
                return last_bp; // 그 위치를 반환한다.
        }

    // 힙 끝까지 갔는데 못 찾았다면,
    // 다시 heap 처음부터 → 탐색 시작점 직전까지 한 바퀴 돌아온다.
    
    for (last_bp = heap_listp; last_bp < cur_bp; last_bp = NEXT_BLKP(last_bp)) 
    {
        if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp)))) 
            return last_bp; 
    }
    return NULL; 
} 

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        // 앞부분 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 남은 블록 생성
        void *next = NEXT_BLKP(bp);
        size_t remainder = csize - asize;
        PUT(HDRP(next), PACK(remainder, 0));
        PUT(FTRP(next), PACK(remainder, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 조절
    size_t extendsize; // 맞지 않을경우 확장할 양
    char *bp;

    //잘못된 요청 무시
    if(size == 0)
        return NULL;

    // 오버헤드 포함해서 블럭 사이즈 조절함
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE *((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 알맞는 가용 리스트 탐색
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // 맞지않음 더 많은 메모리 확보하고 다른 블럭으로 고고씽
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp; 
}
////////////////////////mm_free///////////////////////////////////////
/* mm_free - Freeing a block does nothing.*/
void mm_free(void *ptr) //해제하려는 포인터
{
    size_t size = GET_SIZE(HDRP(ptr));//해제하려는 블록의 헤더에서 크기 정보를 가져오기

    PUT(HDRP(ptr), PACK(size, 0)); // 헤더에 size 0 넣고 가용가능하다는걸 기입
    PUT(FTRP(ptr), PACK(size, 0)); // 풋터에도 같은내용을 써주고 (이 부분은 병합 과정에서 판단할 때 사용)
    coalesce(ptr);
}
//////////////////////// coalesce  ///////////////////////////////////
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 가용 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 가용 상태
    size_t size = GET_SIZE(HDRP(bp));

    // CASE 1 : 양쪽 꽉 막힘
    if(prev_alloc && next_alloc){
        return bp;
    }
    // CASE 2 : 뒤가 비었음
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // CASE 3 : 앞이 비었음
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // CASE 4 : 양쪽 텅텅
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 양쪽 사이즈 더 해주고
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 왼쪽 메모리 블록의 헤더를 변경(왜냐? 그 블록의 헤더는 이제 합쳐진 하나의 블록의 헤더거든)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 오른쪽 메모리 블록의 푸터를 변경(왜냐? 그 블록의 푸터는 이제 합쳐진 하나의 블록의 푸터거든)
        bp = PREV_BLKP(bp);
    }

    last_bp = bp; // 병합한것을 last_bp 갱신
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

