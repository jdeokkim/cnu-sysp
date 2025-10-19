/*
 * mm-implicit.c - An implicit free list allocator for `malloc()`. 
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
// #define DEBUG

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

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */

#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

/* Return the maximum value between `x` and `y`. */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address `p`. */
#define GET(p)      (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (val))

/* Read the size and allocated fields from address `p`. */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr `bp`, compute address of its header and footer. */
#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr `bp`, compute address of next and previous blocks. */
#define NEXT_BLKP(bp) ((char *) (bp) + GET_SIZE(((char *) (bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE)))

/* Private variables */

/* 
 * A global pointer variable that points to the first word, the first 
 * regular block, and the cached regular block of the implicit free list.
 */
static char *heap_ptr = NULL, *first_bp = NULL, *cached_bp = NULL;

/* Private function prototypes */

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t adj_size);

static void place(void *bp, size_t adj_size);

/* Public functions */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* 힙 메모리 영역을 초기화한다. */
    if ((heap_ptr = mem_sbrk(4 * WSIZE)) == (void *) -1) return -1;

    PUT(heap_ptr + (0 * WSIZE), 0);               // 패딩 데이터
    PUT(heap_ptr + (1 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 헤더
    PUT(heap_ptr + (2 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 푸터
    PUT(heap_ptr + (3 * WSIZE), PACK(0, 1));      // 에필로그 헤더

    // 이제 `first_bp`는 프롤로그 푸터를 가리킨다.
    first_bp = cached_bp = heap_ptr + (2 * WSIZE);

#ifdef DEBUG
    dbg_printf("> mm_init(): \n"), mm_checkheap(1);
#endif

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
    if (size == 0) return NULL;

    char *bp = NULL;

    size_t adj_size = (size > DSIZE)
                          ? (DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE))
                          : (DSIZE << 1); /* 블록의 최소 크기 */

#ifdef DEBUG
    dbg_printf("> malloc() #1: \n"), mm_checkheap(1);
#endif

    if ((bp = find_fit(adj_size)) != NULL) {
        // 적절한 가용 블록을 찾았으므로, 이 블록을 할당한다.
        place(bp, adj_size);

#ifdef DEBUG
        dbg_printf("> malloc() #2.1: \n"), mm_checkheap(1);
#endif

        return bp;
    } else {
        // 가용 블록이 없으므로, 힙 메모리 영역을 확장한다.
        size_t ext_size = MAX(adj_size, CHUNKSIZE);

        if ((bp = extend_heap(ext_size / WSIZE)) != NULL) {
            place(bp, adj_size);

#ifdef DEBUG
            dbg_printf("> malloc() #2.2: \n"), mm_checkheap(1);
#endif

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

#ifdef DEBUG
    dbg_printf("> free() #1: \n"), mm_checkheap(1);
#endif

    // 블록 헤더와 푸터에 설정된 할당 비트를 제거한다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

#ifdef DEBUG
    dbg_printf("> free() #2: \n"), mm_checkheap(1);
#endif

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
#ifdef DEBUG
    dbg_printf("> realloc() #1: \n"), mm_checkheap(1);
#endif

    if (new_size == 0) {
        free(ptr);

        return NULL;
    }

    void *new_ptr = malloc(new_size);

    if (ptr == NULL || new_ptr == NULL) return new_ptr;

    size_t size = GET_SIZE(HDRP(ptr));

    if (size > new_size) size = new_size;

#ifdef DEBUG
    dbg_printf("> realloc() #2: \n"), mm_checkheap(1);
#endif

    memcpy(new_ptr, ptr, size);

#ifdef DEBUG
    dbg_printf("> realloc() #3: \n"), mm_checkheap(1);
#endif

    free(ptr);

#ifdef DEBUG
    dbg_printf("> realloc() #4: \n"), mm_checkheap(1);
#endif

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

#ifdef DEBUG
    dbg_printf("> calloc() \n"), mm_checkheap(1);
#endif

    return bp;
}

/*
 * Check the heap for correctness.
 */
void mm_checkheap(int verbose) {
    void *bp = heap_ptr + (2 * WSIZE);

    // 패딩 바이트를 검사한다.
    assert(GET(heap_ptr + (0 * WSIZE)) == 0);

    // 프롤로그 헤더를 검사한다.
    assert(GET_SIZE(HDRP(bp)) == DSIZE);
    assert(GET_ALLOC(HDRP(bp)));

    if (verbose)
        dbg_printf("| [PADDING] %u |\n"
                   "| [PROLOGUE.HDR <%c>] %u: %u "
                   "| [PROLOGUE.FTR] %u: %u |\n",
                   GET(heap_ptr + (0 * WSIZE)),
                   (bp == first_bp) ? '!' : '_',
                   GET_SIZE(HDRP(bp)),
                   GET_ALLOC(HDRP(bp)),
                   GET_SIZE(FTRP(bp)),
                   GET_ALLOC(HDRP(bp)));

    // 각 블록을 차례대로 확인한다.
    for (bp = first_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            dbg_printf("| [BLOCK.HDR <%c>] %u: %u "
                       "| [BLOCK.DATA] %u bytes "
                       "| [BLOCK.FTR] %u: %u |\n",
                       (bp == first_bp) ? '!' : '_',
                       GET_SIZE(HDRP(bp)),
                       GET_ALLOC(HDRP(bp)),
                       GET_SIZE(HDRP(bp)) - DSIZE,
                       GET_SIZE(FTRP(bp)),
                       GET_ALLOC(FTRP(bp)));

        assert(GET(HDRP(bp)) == GET(FTRP(bp)));
    }

    // 에필로그 헤더를 검사한다.
    assert(GET_SIZE(HDRP(bp)) == 0);
    assert(GET_ALLOC(HDRP(bp)));

    if (verbose)
        dbg_printf("| [EPILOGUE.HDR] %u: %u |\n\n",
                   GET_SIZE(HDRP(bp)),
                   GET_ALLOC(HDRP(bp)));

    bp = cached_bp;

    // 이전 탐색 결과 블록을 확인한다.
    if (bp != NULL) {
        if (verbose)
            dbg_printf("| [BLOCK.HDR <^>] %u: %u "
                       "| [BLOCK.DATA] %u bytes "
                       "| [BLOCK.FTR] %u: %u |\n\n",
                       GET_SIZE(HDRP(bp)),
                       GET_ALLOC(HDRP(bp)),
                       GET_SIZE(HDRP(bp)) - DSIZE,
                       GET_SIZE(FTRP(bp)),
                       GET_ALLOC(FTRP(bp)));

        assert(GET(HDRP(bp)) == GET(FTRP(bp)));
    }
}

/* Private functions */

/*
 * Coalesce this block with adjacent free block(s).
 */
static void *coalesce(void *bp) {
    // 이전 블록과 다음 블록의 할당 비트를 확인한다.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (prev_alloc && next_alloc) return bp;

    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {
        /* 
		 * Case 2: 이전 블록은 비가용, 다음 블록은 가용인 경우...?
		 */

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /*
		 * Case 3: 이전 블록은 가용, 다음 블록은 비가용인 경우...?
		 */

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    } else {
        /*
		 * Case 4: 이전 블록과 다음 블록이 둘 다 가용인 경우...?
		 */

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    /* 
	 * 이전 블록의 크기가 `(DSIZE << 1)`보다 작다는 것은
	 * 그 블록이 프롤로그 블록임을 뜻한다.
	 */
    if (GET_SIZE(PREV_BLKP(bp)) < (DSIZE << 1)) first_bp = bp;

    /*
	 * 이전 탐색 종료 위치가 블록의 페이로드 시작 위치가
	 * 아닌 페이로드 내부의 다른 위치를 가리키고 있다면, 
	 * 그 위치를 재설정한다.
	 */
    if ((cached_bp > (char *) bp) && (cached_bp < NEXT_BLKP(bp)))
        cached_bp = bp;

#ifdef DEBUG
    dbg_printf("> coalesce(): \n"), mm_checkheap(1);
#endif

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

    char *bp = mem_sbrk(size);

    if (bp == (char *) -1) return NULL;

    PUT(HDRP(bp), PACK(size, 0));          // 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));          // 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 에필로그 푸터

#ifdef DEBUG
    dbg_printf("> extend_heap(): \n"), mm_checkheap(1);
#endif

    return coalesce(bp);
}

/*
 * Perform a (first / next / best)-fit search of the implicit free list.
 */
static void *find_fit(size_t adj_size) {
    // 이전 탐색 종료 위치에 해당하는 블록부터 차례대로 확인한다.
    for (void *bp = cached_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (GET_SIZE(HDRP(bp)) >= adj_size && !GET_ALLOC(HDRP(bp))) {
            dbg_printf("> find_fit() #1: Found:\n"
                       "| [BLOCK.HDR] %u: %u\n\n",
                       GET_SIZE(HDRP(bp)),
                       GET_ALLOC(HDRP(bp)));

            return (cached_bp = bp);
        }

    // 이제 첫 번째 가용 블록부터 이전 탐색 종료 위치 직전까지 확인한다.
    for (void *bp = first_bp; bp < (void *) cached_bp; bp = NEXT_BLKP(bp))
        if (GET_SIZE(HDRP(bp)) >= adj_size && !GET_ALLOC(HDRP(bp))) {
            dbg_printf("> find_fit() #2: Found:\n"
                       "| [BLOCK.HDR] %u: %u\n\n",
                       GET_SIZE(HDRP(bp)),
                       GET_ALLOC(HDRP(bp)));

            return (cached_bp = bp);
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

#ifdef DEBUG
    dbg_printf("> place() #1: \n"), mm_checkheap(1);
#endif

    // 가용 블록의 크기와 할당 요청 크기를 비교한다.
    if (remainder < (DSIZE << 1)) {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    } else {
        PUT(HDRP(bp), PACK(adj_size, 1));
        PUT(FTRP(bp), PACK(adj_size, 1));

        bp = NEXT_BLKP(bp);

        // 이 블록은 가용 블록이 된다.
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
    }

#ifdef DEBUG
    dbg_printf("> place() #2: \n"), mm_checkheap(1);
#endif
}
