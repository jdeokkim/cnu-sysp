/*
 * mm-explicit.c - An explicit free list allocator for `malloc()`.
 *
 * Author: Jaedeok Kim (https://github.com/jdeokkim)
 * Date: 2023-11-28
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
//#define DEBUG

#ifdef DEBUG
    #define dbg_printf(...) printf(__VA_ARGS__)
#else
    #define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
    /* create aliases for driver tests */
    #define malloc  mm_malloc
    #define free    mm_free
    #define realloc mm_realloc
    #define calloc  mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */

/* Word size and double word size (bytes) */
#define WSIZE 4
#define DSIZE 8

/* Header and footer size (bytes) */
#define HDRSIZE WSIZE
#define FTRSIZE WSIZE

/* Overhead of a header and a footer (bytes) */
#define OVERHEAD (HDRSIZE + FTRSIZE)

/* Extend heap by this amount (bytes) */
#define CHUNKSIZE (1 << 12)

/* Return the maximum value between `x` and `y`. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Return the minimum value between `x` and `y`. */
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address `p`. */
#define GET(p)      (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (val))

/* Read and write a double word at address `p`. */
#define GET8(p)      (*(unsigned long *) (p))
#define PUT8(p, val) (*(unsigned long *) (p) = (val))

/* Read the size and allocated fields from address `p`. */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr `bp`, compute address of its header and footer. */
#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 
 * Given block ptr `bp`, compute address of next and previous 
 * free block pointers. 
 */
#define NEXT_FREEP(bp) ((char *) (bp))
#define PREV_FREEP(bp) ((char *) (bp) + DSIZE)

/* Given block ptr `bp`, compute address of next and previous free blocks. */
#define NEXT_FREE_BLKP(bp) ((char *) GET8((char *) (bp)))
#define PREV_FREE_BLKP(bp) ((char *) GET8((char *) (bp) + DSIZE))

/* Given block ptr `bp`, compute address of next and previous blocks. */
#define NEXT_BLKP(bp) ((char *) (bp) + GET_SIZE((char *) (bp) - WSIZE))
#define PREV_BLKP(bp) ((char *) (bp) - GET_SIZE((char *) (bp) - DSIZE))

/* Private variables */

/*
 * A global pointer variable that points to the first 
 * free block of the explicit free list.
 */
static char *heap_ptr = NULL;

/* Private function prototypes */

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t adj_size);

static void place(void *bp, size_t adj_size);

static void insert_into_list(void *bp);
static void remove_from_list(void *bp);

static void print_block(const void *bp, const char *pfx, int eol);

/* Public functions */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    int incr = WSIZE + (OVERHEAD + (DSIZE << 1)) + HDRSIZE;

    /* 힙 메모리 영역을 초기화한다. */
    if ((heap_ptr = mem_sbrk(incr)) == (void *) -1) return -1;

    PUT8(heap_ptr, (unsigned long) NULL);          // 첫 번째 가용 블록
    PUT8(heap_ptr + DSIZE, (unsigned long) NULL);  // 마지막 가용 블록

    PUT(heap_ptr + (DSIZE << 1), 0);  // 패딩 데이터

    heap_ptr += ((DSIZE << 1) + WSIZE);

    PUT(heap_ptr, PACK(OVERHEAD, 1));                 // 프롤로그 헤더
    PUT(heap_ptr + HDRSIZE, PACK(OVERHEAD, 1));       // 프롤로그 푸터
    PUT(heap_ptr + (HDRSIZE + FTRSIZE), PACK(0, 1));  // 에필로그 헤더

    heap_ptr -= ((DSIZE << 1) + WSIZE);

    dbg_printf("> mm_init(): \n");
    mm_checkheap(1);

    // `CHUNKSIZE`만큼 힙 메모리 영역을 확장한다.
    return (extend_heap(CHUNKSIZE / WSIZE) != NULL) - 1;
}

/*
 * Allocates `size` bytes of uninitialized storage.
 *
 * If allocation succeeds, returns a pointer that is suitably aligned
 * for any object type with fundamental alignment.
 *
 * If `size` is zero, the behavior of `malloc()` is implementation-defined.
 *
 * For example, a null pointer may be returned. Alternatively,
 * a non-null pointer may be returned; but such a pointer should not
 * be dereferenced, and should be passed to `free()` to avoid memory leaks.
 */
void *malloc(size_t size) {
    if (size == (size_t) 0) return NULL;

    char *bp = NULL;

    size_t adj_size = (size > (DSIZE << 1))
                          ? DSIZE * ((size + OVERHEAD + (DSIZE - 1)) / DSIZE)
                          : (OVERHEAD + (DSIZE << 1));

    dbg_printf("> malloc() #1: \n");
    mm_checkheap(1);

    if ((bp = find_fit(adj_size)) != NULL) {
        dbg_printf("> malloc() #2.1: \n");
        mm_checkheap(1);

        // 적절한 가용 블록을 찾았으므로, 이 블록을 할당한다.
        place(bp, adj_size);

        dbg_printf("> malloc() #2.2: \n");
        mm_checkheap(1);

        return bp;
    } else {
        // 가용 블록이 없으므로, 힙 메모리 영역을 확장한다.
        size_t ext_size = MAX(adj_size, CHUNKSIZE);

        if ((bp = extend_heap(ext_size / WSIZE)) != NULL) {
            dbg_printf("> malloc() #2.3: \n");
            mm_checkheap(1);

            place(bp, adj_size);

            dbg_printf("> malloc() #2.4: \n");
            mm_checkheap(1);

            return bp;
        }

        return NULL;
    }
}

/*
 * Deallocates the space previously allocated by `malloc()`, `calloc()`,
 * `aligned_alloc()`, (since C11) or `realloc()`.
 *
 * If `ptr` is a null pointer, the function does nothing.
 */
void free(void *ptr) {
    if (ptr == NULL) return;

    size_t size = GET_SIZE(HDRP(ptr));

    dbg_printf("> free() #1: \n");
    mm_checkheap(1);

    // 블록 헤더와 푸터에 설정된 할당 비트를 제거한다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // PUT8(NEXT_FREEP(ptr), (unsigned long) NULL);
    // PUT8(PREV_FREEP(ptr), (unsigned long) NULL);

    dbg_printf("> free() #2: \n");
    mm_checkheap(1);

    coalesce(ptr);
}

/*
 * Reallocates the given area of memory. If `ptr` is not `NULL`, it must
 * be previously allocated by `malloc()`, `calloc()` or `realloc()` and
 * not yet freed with a call to `free()` or `realloc()`. Otherwise,
 * the results are undefined.
 *
 * The reallocation is done by either:
 *   a) expanding or contracting the existing area pointed to by `ptr`,
 *   if possible. The contents of the area remain unchanged up to the
 *   lesser of the new and old sizes. If the area is expanded,
 *   the contents of the new part of the array are undefined.
 *
 *   b) allocating a new memory block of size `new_size` bytes, copying
 *   memory area with size equal the lesser of the new and the old sizes,
 *   and freeing the old block.
 *
 * If there is not enough memory, the old memory block is not freed and
 * null pointer is returned.
 *
 * If `ptr` is `NULL`, the behavior is the same as calling `malloc(new_size)`.
 *
 * Otherwise,
 *
 * > if `new_size` is zero, the behavior is implementation defined (null
 *   pointer may be returned (in which case the old memory block may or may not
 *   be freed), or some non-null pointer may be returned that may not be used
 *   to access storage). Such usage is deprecated. (since C17)
 */
void *realloc(void *ptr, size_t new_size) {
    if (new_size == (size_t) 0) {
        free(ptr);

        return NULL;
    }

    void *new_ptr = malloc(new_size);

    if (ptr == NULL || new_ptr == NULL) return new_ptr;

    size_t size = GET_SIZE(HDRP(ptr));

    if (size > new_size) size = new_size;

    memcpy(new_ptr, ptr, size);

    free(ptr);

    return new_ptr;
}

/*
 * Allocates memory for an array of `num` objects of `size` and initializes
 * all bytes in the allocated storage to zero.
 *
 * If allocation succeeds, returns a pointer to the lowest (first) byte
 * in the allocated memory block that is suitably aligned for any object
 * type with fundamental alignment.
 *
 * If `size` is zero, the behavior is implementation defined (null pointer
 * may be returned, or some non-null pointer may be returned that may not
 * be used to access storage).
 */
void *calloc(size_t num, size_t size) {
    size *= num;

    void *bp = malloc(size);

    memset(bp, 0, size);

    return bp;
}

/*
 * Check the heap for correctness.
 */
void mm_checkheap(int verbose) {
#ifdef DEBUG
    // 패딩 바이트를 검사한다.
    assert(GET(heap_ptr + (DSIZE << 1)) == 0);

    void *bp = heap_ptr + ((DSIZE << 1) + (WSIZE + HDRSIZE));

    // 프롤로그 헤더를 검사한다.
    assert(GET_SIZE(HDRP(bp)) == OVERHEAD);
    assert(GET_ALLOC(HDRP(bp)));

    // 프롤로그 푸터를 검사한다.
    assert(GET(HDRP(bp)) == GET(FTRP(bp)));

    if (verbose)
        dbg_printf("| [ROOT.HEAD] <%p> "
                   "| [ROOT.TAIL] <%p> "
                   "| [PADDING] %u |\n"
                   "| [PROLG.HDR <%p>] %u: %u "
                   "| [PROLG.FTR] %u: %u |\n",
                   (void *) GET8(heap_ptr),
                   (void *) GET8(heap_ptr + DSIZE),
                   GET(heap_ptr + (DSIZE << 1)),
                   bp,
                   GET_SIZE(HDRP(bp)),
                   GET_ALLOC(HDRP(bp)),
                   GET_SIZE(FTRP(bp)),
                   GET_ALLOC(FTRP(bp)));

    // 모든 블록의 헤더와 푸터를 검사한다.
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    #if 1
        if (verbose) print_block(bp, NULL, 0);
    #endif
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));
    }

    void *fbp = (void *) GET8(heap_ptr);

    if (fbp != NULL) {
        dbg_printf("===========================================\n");

        // 가용 블록의 헤더와 푸터, 그리고 링크 포인터를 검사한다.
        for (; fbp != NULL; fbp = NEXT_FREE_BLKP(fbp)) {
            assert((fbp > mem_heap_lo()) && (fbp < mem_heap_hi()));

            if (verbose) print_block(fbp, "FREE", 0);
        }

        dbg_printf("===========================================\n");
    }

    // 에필로그 헤더를 검사한다.
    assert(GET_SIZE(HDRP(bp)) == 0);
    assert(GET_ALLOC(HDRP(bp)));

    if (verbose)
        dbg_printf("| [EPILG.HDR <%p>] %u: %u |\n\n",
                   bp,
                   GET_SIZE(HDRP(bp)),
                   GET_ALLOC(HDRP(bp)));
#endif
}

/* Private functions */

/*
 * Coalesce this block with adjacent free block(s).
 */
static void *coalesce(void *bp) {
    dbg_printf("> coalesce() #1: \n");
    mm_checkheap(1);

    // 이전 블록과 다음 블록의 할당 비트를 확인한다.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {
        /*
         * Case 2: 이전 블록은 비가용, 다음 블록은 가용인 경우...?
         */

        remove_from_list(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /*
         * Case 3: 이전 블록은 가용, 다음 블록은 비가용인 경우...?
         */

        remove_from_list(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    } else if (!prev_alloc && !next_alloc) {
        /*
         * Case 4: 이전 블록과 다음 블록이 둘 다 가용인 경우...?
         */

        remove_from_list(NEXT_BLKP(bp)), remove_from_list(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    insert_into_list(bp);

    dbg_printf("> coalesce() #2: \n");
    mm_checkheap(1);

    return bp;
}

/*
 * Extend the heap with a new free block.
 */
static void *extend_heap(size_t words) {
    /*
     * 정렬 유지를 위해 블록 크기를 항상 짝수 개의
     * 워드로 설정한다.
     */
    size_t size = (words + (words & 1)) * WSIZE;

    void *bp = mem_sbrk(size);

    if (bp == (char *) -1) return NULL;

    dbg_printf("> extend_heap() #1: \n");
    mm_checkheap(1);

    PUT(HDRP(bp), PACK(size, 0));          // 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));          // 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 에필로그 푸터

    dbg_printf("> extend_heap() #2: \n");
    mm_checkheap(1);

    return coalesce(bp);
}

/*
 * Perform a (first / next / best)-fit search of the explicit free list.
 */
static void *find_fit(size_t adj_size) {
    void *fbp = (void *) GET8(heap_ptr);

    // 직접 리스트의 첫 번째 가용 블록부터 차례대로 확인한다.
    for (; fbp != NULL && !GET_ALLOC(HDRP(fbp)); fbp = NEXT_FREE_BLKP(fbp)) {
        if ((GET_SIZE(HDRP(fbp)) >= adj_size)) {
            dbg_printf("> find_fit(): Found:\n");
            print_block(fbp, NULL, 1);

            return fbp;
        }
    }

    dbg_printf("> find_fit(): Not found...\n\n");

    return NULL;
}

/*
 * Place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or
 * exceed the minimum block size.
 */
static void place(void *bp, size_t adj_size) {
    size_t size = GET_SIZE(HDRP(bp)), remainder = size - adj_size;

    dbg_printf("> place() #1: \n");
    mm_checkheap(1);

    // 비가용 블록은 가용 리스트에서 제거한다.
    remove_from_list(bp);

    // 가용 블록의 크기와 할당 요청 크기를 비교한다.
    if (remainder < (OVERHEAD + (DSIZE << 1))) {
        dbg_printf("> place() #2.1: \n");
        print_block(bp, NULL, 1);

        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));

        dbg_printf("> place() #2.2: \n");
        print_block(bp, NULL, 1);
    } else {
        dbg_printf("> place() #2.3: \n");
        print_block(bp, NULL, 1);

        PUT(HDRP(bp), PACK(adj_size, 1));
        PUT(FTRP(bp), PACK(adj_size, 1));

        dbg_printf("> place() #2.4: \n");
        print_block(bp, NULL, 1);

        bp = NEXT_BLKP(bp);

        // 이 블록은 가용 블록이 된다.
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));

        dbg_printf("> place() #2.5: \n");
        print_block(bp, NULL, 1);

        // 가용 리스트에 블록을 삽입한다.
        insert_into_list(bp);
    }

    dbg_printf("> place() #3: \n");
    mm_checkheap(1);
}

/*
 * Insert the freed block at the beginning of the free list.
 */
static void insert_into_list(void *bp) {
    if (bp == NULL || GET_ALLOC(FTRP(bp))) return;

    void *fbp = (void *) GET8(heap_ptr);

    dbg_printf("> insert_into_list() #1: \n");
    mm_checkheap(1);

    if (bp != fbp) {
        dbg_printf("> insert_into_list() #2.1: \n");
        mm_checkheap(1);

        // `fbp`의 이전 링크를 변경한다.
        if (fbp != NULL) {
            PUT8(PREV_FREEP(fbp), (unsigned long) bp);

            dbg_printf("> insert_into_list() #2.2: \n");
            print_block(fbp, "FREE", 1);
        }

        // `bp`의 다음 링크를 변경한다.
        PUT8(NEXT_FREEP(bp), (unsigned long) fbp);

        dbg_printf("> insert_into_list() #2.3: \n");
        print_block(bp, NULL, 1);
    }

    // `bp`의 이전 링크를 설정한다.
    PUT8(PREV_FREEP(bp), (unsigned long) NULL);

    dbg_printf("> insert_into_list() #3: \n");
    print_block(bp, NULL, 1);

    // 이제 `bp`는 첫 번째 가용 블록이 된다.
    PUT8(heap_ptr, (unsigned long) bp);

    dbg_printf("> insert_into_list() #4: \n");
    mm_checkheap(1);
}

/*
 * Remove the block from the free list.
 */
static void remove_from_list(void *bp) {
    if (bp == NULL) return;

    dbg_printf("> remove_from_list() #1: \n");
    print_block(bp, NULL, 1);

    void *next_fbp = NEXT_FREE_BLKP(bp), *prev_fbp = PREV_FREE_BLKP(bp);

    if (prev_fbp != NULL && !GET_ALLOC(HDRP(prev_fbp))) {
        // `prev_fbp`의 다음 링크를 변경한다.
        PUT8(NEXT_FREEP(prev_fbp), (unsigned long) next_fbp);

        dbg_printf("> remove_from_list() #2.1: \n");
        print_block(prev_fbp, NULL, 1);
    }

    if (next_fbp != NULL && !GET_ALLOC(HDRP(next_fbp))) {
        // `next_fbp`의 이전 링크를 변경한다.
        PUT8(PREV_FREEP(next_fbp), (unsigned long) prev_fbp);

        dbg_printf("> remove_from_list() #2.2: \n");
        print_block(next_fbp, NULL, 1);
    }

    // `bp`가 첫 번째 가용 블록일 경우...?
    if (bp == (void *) GET8(heap_ptr))
        PUT8(heap_ptr, (unsigned long) next_fbp);

    dbg_printf("> remove_from_list() #3: \n");
    mm_checkheap(1);
}

/*
 * Print the details of the block. 
 */
static void print_block(const void *bp, const char *pfx, int eol) {
    if (pfx == NULL) pfx = "BLOCK";

    dbg_printf("| [%s.HDR <%p>] %u: %u "
               "| [%s.NEXT] %p "
               "| [%s.PREV] %p "
               "| [%s.FTR] %u: %u |\n",
               pfx,
               bp,
               GET_SIZE(HDRP(bp)),
               GET_ALLOC(HDRP(bp)),
               pfx,
               !GET_ALLOC(HDRP(bp)) ? NEXT_FREE_BLKP(bp) : NULL,
               pfx,
               !GET_ALLOC(HDRP(bp)) ? PREV_FREE_BLKP(bp) : NULL,
               pfx,
               GET_SIZE(FTRP(bp)),
               GET_ALLOC(FTRP(bp)));

    if (eol) dbg_printf("\n");
}
