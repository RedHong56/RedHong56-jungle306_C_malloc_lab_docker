/*
 * Explicit free list malloc (CS:APP style)
 * - 8-byte alignment
 * - header/footer: 4 bytes each
 * - free block payload stores pred/succ pointers (8B + 8B)
 * - minimum free block size = 24B (3*DSIZE)
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

/* Team info (course-provided struct) */
team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

/* Alignment & basic sizes */
#define ALIGNMENT 8
#define WSIZE     4            /* header/footer */
#define DSIZE     8            /* double word */
#define CHUNKSIZE (1<<12)      /* heap extend size (bytes) */

#define MAX(x,y) ((x)>(y)?(x):(y))

/* Pack size and alloc bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read/Write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read size/alloc from header/footer at p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* Given block ptr bp, compute header/footer ptrs */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute next/prev block ptrs */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Explicit-list pred/succ fields inside free block payload */
#define PRED(bp)            (*(char **)(bp))
#define SUCC(bp)            (*(char **)((char *)(bp) + DSIZE))

/* Policy: minimum free block size must hold pred+succ = 16B plus hdr/ftr = 8B -> 24B */
#define MIN_FREE_BLK        (3*DSIZE)

/* Globals */
static char *heap_listp = NULL;           /* prologue payload pointer */
static void *free_list_head = NULL;       /* explicit free list head */
static void *last_bp;

/* Internal helpers */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void  place(void *bp, size_t asize);
static void  insert_free_block(void *bp);
static void  remove_free_block(void *bp);

/* mm_init */
int mm_init(void)
{
    /* Create initial empty heap: prologue + epilogue */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                              /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));     /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));     /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));         /* Epilogue header */
    heap_listp += (2*WSIZE);

    free_list_head = NULL;
    last_bp = heap_listp;
    /* Extend the heap with a free block */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* extend_heap: keep alignment (even # of words) */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size = (words % 2) ? (words+1)*WSIZE : words*WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize the new free block and epilogue */
    PUT(HDRP(bp), PACK(size, 0));                 /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));                 /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));         /* New epilogue header */

    /* Coalesce with previous if possible, and insert */
    return coalesce(bp);
}

/* find_fit: best-fit over explicit free list only */
static void *find_fit(size_t asize)
{
    void *best = NULL;
    size_t bestsz = (size_t)-1;

    for (void *p = free_list_head; p != NULL; p = SUCC(p)) {
        size_t sz = GET_SIZE(HDRP(p));
        if (sz >= asize && sz < bestsz) {
            best = p;
            bestsz = sz;
            if (bestsz == asize) break; // perfect fit
        }
    }
    return best;
}


/* place: allocate asize in bp; split if remainder can hold a free block */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free_block(bp);

    if (csize - asize >= MIN_FREE_BLK) {
        /* allocate the front part */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* create the remainder as a new free block */
        void *nbp = NEXT_BLKP(bp);
        size_t rsize = csize - asize;
        PUT(HDRP(nbp), PACK(rsize, 0));
        PUT(FTRP(nbp), PACK(rsize, 0));
        PRED(nbp) = NULL;
        SUCC(nbp) = NULL;
        insert_free_block(nbp);
    } else {
        /* allocate whole block */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* mm_malloc */
void *mm_malloc(size_t size)
{
    if (size == 0) return NULL;

    /* Adjust block size: header+footer included, 8B aligned */
    size_t asize;
    if (size <= DSIZE) asize = 3*DSIZE;  /* 24B allocated OK */
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* For free blocks (when split happens) we enforce MIN_FREE_BLK on the remainder,
       but allocated block can be 16B (header+footer+8B payload). */

    void *bp = find_fit(asize);
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    size_t extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* mm_free */
void mm_free(void *ptr)
{
    if (ptr == NULL) return;

    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/* coalesce: safe prev boundary check, maintain free list */
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    /* Safe prev_alloc computation: if prev would cross prologue, treat as allocated */
    size_t prev_alloc;
    if (HDRP(PREV_BLKP(bp)) < (heap_listp - WSIZE)) {  /* prologue payload = heap_listp; prologue hdr at heap_listp-WSIZE */
        prev_alloc = 1;
    } else {
        prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (prev_alloc && next_alloc) {
        /* Case 1: both allocated */
        PRED(bp) = NULL; SUCC(bp) = NULL;
        insert_free_block(bp);
        last_bp = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        /* Case 2: merge with next */
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        /* Case 3: merge with prev */
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        /* Case 4: merge both sides */
        remove_free_block(NEXT_BLKP(bp));
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    PRED(bp) = NULL; SUCC(bp) = NULL;
    insert_free_block(bp);
    last_bp = bp;
    return bp;
}

/* mm_realloc: in-place grow using next free block when possible, else malloc+copy */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) { mm_free(ptr); return NULL; }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    void *next = NEXT_BLKP(ptr);

    /* Compute requested allocated size (same rounding as malloc’s allocated block) */
    size_t asize;
    if (size <= DSIZE) asize = 3*DSIZE;                           /* allocated block can be 16B */
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Copy size = min(old payload, requested payload) */
    size_t copy = oldsize - DSIZE;
    if (size < copy) copy = size;

    /* Try in-place expand if next is free and combined is enough */
    if (!GET_ALLOC(HDRP(next))) {
        size_t nextsz = GET_SIZE(HDRP(next));
        size_t newsz  = oldsize + nextsz;

        if (newsz >= asize) {
            remove_free_block(next);
            size_t remain = newsz - asize;

            if (remain >= MIN_FREE_BLK) {
                /* allocate front portion, leave a proper free remainder */
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                void *rbp = NEXT_BLKP(ptr);
                PUT(HDRP(rbp), PACK(remain, 0));
                PUT(FTRP(rbp), PACK(remain, 0));
                PRED(rbp) = NULL; SUCC(rbp) = NULL;
                insert_free_block(rbp);
            } else {
                /* absorb entire next (no remainder) */
                PUT(HDRP(ptr), PACK(newsz, 1));
                PUT(FTRP(ptr), PACK(newsz, 1));
            }
            return ptr;
        }
    }

    /* fallback: new alloc + copy */
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    memcpy(newptr, ptr, copy);
    mm_free(ptr);
    return newptr;
}

/* --- explicit free list ops (LIFO insert at head recommended) --- */

static void insert_free_block(void *bp)
{
    /* sanity: free block shape */
    assert(GET_ALLOC(HDRP(bp)) == 0);
    assert(GET_SIZE(HDRP(bp)) >= MIN_FREE_BLK);

    /* LIFO insert at head (fast) */
    PRED(bp) = NULL;
    SUCC(bp) = free_list_head;
    if (free_list_head != NULL) PRED(free_list_head) = bp;
    free_list_head = bp;
}

static void remove_free_block(void *bp)
{
    void *pred = PRED(bp);
    void *succ = SUCC(bp);

    if (pred == NULL) {
        /* removing head */
        free_list_head = succ;
        if (succ) PRED(succ) = NULL;
    } else {
        SUCC(pred) = succ;
        if (succ) PRED(succ) = pred;
    }

    /* clean dangling links (helps catch double-removal) */
    PRED(bp) = NULL;
    SUCC(bp) = NULL;
}
