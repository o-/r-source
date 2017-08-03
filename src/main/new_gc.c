#include <stdint.h>
#include <stdlib.h>

#define USE_RINTERNALS

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#define R_USE_SIGNALS 1
#include <Defn.h>
#include <Internal.h>
#include <R_ext/GraphicsEngine.h> /* GEDevDesc, GEgetDevice */
#include <R_ext/Rdynload.h>
#include <R_ext/Rallocators.h> /* for R_allocator_t structure */
#include <Rmath.h>             // R_pow_di
#include <Print.h>             // R_print
#include <sys/mman.h>

#ifdef COMPUTE_REFCNT_VALUES
#define INIT_REFCNT(x) do {			\
	SEXP __x__ = (x);			\
	SET_REFCNT(__x__, 0);			\
	SET_TRACKREFS(__x__, TRUE);		\
    } while (0)
#else
#define INIT_REFCNT(x) do {} while (0)
#endif

#define PAGE_SIZE 0x2000L
#define PAGE_IDX 32
#define PAGE_IDX_BITS 5
#define PAGE_MASK 0x1fff
#define MAX_IDX (PAGE_SIZE / PAGE_IDX)

// #define GCPROF 1
// #define GCDEBUG

#ifdef GCDEBUG
#define CHECK(exp)                \
  if (!(exp)) {                   \
    printf("err %d\n", __LINE__); \
    asm("int3");                  \
  }
#define ON_DEBUG(exp) exp
#else
#define CHECK(exp) \
  {}
#define ON_DEBUG(exp) \
  {}
#endif

struct Page;
typedef struct HashtableEntry {
  struct Page* page;
  uint8_t mark;
} HashtableEntry;

typedef struct Hashtable {
  size_t size;
  size_t bucket_size;
  HashtableEntry data[];
} Hashtable;

void Hashtable_init(Hashtable** ht) {
  size_t size = 64;
  size_t bucket_size = 16;

  size_t sz = sizeof(Hashtable) + size * bucket_size * sizeof(HashtableEntry);
  Hashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  h->bucket_size = bucket_size;
  *ht = h;
}

Rboolean Hashtable_add(Hashtable* ht, struct Page* p, uint8_t);
void Hashtable_grow(Hashtable** ht) {
  Hashtable* old = *ht;
  size_t size = old->size * 2;
  size_t sz =
      sizeof(Hashtable) + size * old->bucket_size * sizeof(HashtableEntry);
  Hashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  h->bucket_size = old->bucket_size;
  size_t max = old->size * old->bucket_size;
  for (size_t i = 0; i < max; ++i) {
    if (old->data[i].page != NULL)
      Hashtable_add(h, old->data[i].page, old->data[i].mark);
  }
  *ht = h;
  free(old);
}

inline uint32_t Hashtable_h(void* k) {
  uint32_t a = (uintptr_t)k >> PAGE_IDX_BITS;
  a = (a ^ 61) ^ (a >> 16);
  a = a + (a << 3);
  a = a ^ (a >> 4);
  a = a * 0x27d4eb2d;
  a = a ^ (a >> 15);
  return a;
}

void Hashtable_occ(Hashtable* ht);
Rboolean Hashtable_add(Hashtable* ht, struct Page* p, uint8_t mark) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size - 1));
  long el = 0;
  while (ht->data[idx + el].page != NULL && el < ht->bucket_size) {
    if (ht->data[idx + el].page == p) {
      R_Suicide("ht err 3");
    }
    ++el;
  }
  if (el == ht->bucket_size) {
    return FALSE;
  }
  CHECK(ht->data[idx + el].page == NULL);
  CHECK(el >= 0 && el < ht->bucket_size);
  HashtableEntry e = {p, mark};
  ht->data[idx + el] = e;
  return TRUE;
}

void Hashtable_set(Hashtable* ht, struct Page* p, uint8_t mark) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size - 1));
  long el = 0;
  while (ht->data[idx + el].page != NULL && el < ht->bucket_size) {
    if (ht->data[idx + el].page == p) {
      ht->data[idx + el].mark = mark;
      return;
    }
    ++el;
  }
  R_Suicide("ht err2");
}

inline uint8_t Hashtable_get(Hashtable* ht, struct Page* p) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size - 1));
  long el = 0;
  while (el < ht->bucket_size && ht->data[idx + el].page != NULL) {
    if (ht->data[idx + el].page == p)
      return ht->data[idx + el].mark;
    ++el;
  }
  R_Suicide("ht err");
}

inline void Hashtable_remove_el(Hashtable* ht, size_t pos) {
  do {
    ht->data[pos] = ht->data[pos + 1];
    ++pos;
  } while (pos % ht->bucket_size != 0);
  ht->data[pos - 1].page = NULL;
}

void Hashtable_remove(Hashtable* ht, void* p) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size - 1));
  long el = 0;
  while (el < ht->bucket_size) {
    if (ht->data[idx + el].page == p) {
      Hashtable_remove_el(ht, idx + el);
      return;
    }
    el++;
  }
  CHECK(0);
}

void Hashtable_occ(Hashtable* ht) {
  size_t used = 0;
  for (size_t i = 0; i < ht->size * ht->bucket_size; ++i) {
    if (ht->data[i].page != NULL)
      ++used;
  }
  printf("HT usage: %f\n", (double)used / (double)(ht->size * ht->bucket_size));
}

#define UNMARKED 0
uint8_t THE_MARK = 1;

static size_t gc_cnt = 0;
Rboolean fullCollection = FALSE;

#define CONS_BUCKET 0
#define ENV_BUCKET 1
#define PROM_BUCKET 2
#define GENERIC_SEXP_BUCKET 3
#define NUM_BUCKETS 19
#define FIRST_GENERIC_BUCKET 4

size_t BUCKET_SIZE[NUM_BUCKETS] = {
  40, 40, 40, 40,
  32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 128, 160, 192, 256, 320};
size_t CELL_ALIGNED[NUM_BUCKETS] = {
  0, 0, 0, 0,
  1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 4, 5, 6, 8, 10};

#define INITIAL_PAGE_LIMIT 800
#define FREE_PAGES_SLACK 800
#define INITIAL_BIG_OBJ_LIMIT (16 * 1024 * 1024)
#define PAGE_FULL_TRESHOLD 0.01
#define GROW_RATE 1.16
#define HEAP_SLACK 0.83
#define FULL_COLLECTION_TRIGGER 0.95
#define WRITE_BARRIER_MS_TRIGGER 2000
#define MS_TRIGGER 1000
#define INITIAL_MS_SIZE 4000

typedef struct Page {
  uint8_t mark[MAX_IDX];
  size_t reclaimed_nodes;
  struct Page* next;
  struct Page* prev;
  uint8_t full;
  uint8_t bkt;
  uint8_t last_mark;
  uintptr_t start;
  uintptr_t end;
  uintptr_t split_page;
  uintptr_t sweep_end;
  uintptr_t alloc_finger;
  uintptr_t sweep_finger;
  size_t available_nodes;
  char data[];
} Page;

typedef struct BigObject {
  uint8_t mark;
  struct BigObject* next;
  size_t size;
  SEXPREC data[];
} BigObject;

#define PTR2PAGE(ptr) ((Page*)((uintptr_t)(ptr) & ~PAGE_MASK))
#define PTR2IDX(ptr) (((uintptr_t)(ptr) & PAGE_MASK) >> PAGE_IDX_BITS)
#define PTR2BIG(ptr) ((BigObject*)((uintptr_t)(ptr) - sizeof(BigObject)))
#define ISNODE(s)                                \
  ((uintptr_t)HEAP.pageArena < (uintptr_t)(s) && \
   (uintptr_t)(s) < HEAP.pageArenaEnd)
#define ISMARKED(s)                                      \
  (ISNODE(s) ? PTR2PAGE(s)->mark[PTR2IDX(s)] == THE_MARK \
             : PTR2BIG(s)->mark == THE_MARK)
#define GETMARK(s) \
  (ISNODE(s) ? &PTR2PAGE(s)->mark[PTR2IDX(s)] : &PTR2BIG(s)->mark)
#define INIT_NODE(s) (*(uint32_t*)&((SEXP)(s))->sxpinfo = 0)

void doGc(unsigned);

typedef struct SizeBucket {
  Page* pages;
  Page* to_bump;
  Page* to_sweep;
  size_t num_pages;
  Hashtable* last_mark;
} SizeBucket;

typedef struct FreePage {
  Page* finger;
  struct FreePage* next;
  Rboolean commited;
} FreePage;

#define MAX_PAGES 600000L
struct {
  SizeBucket sizeBucket[NUM_BUCKETS];
  BigObject* bigObjects;
  size_t page_limit;
  size_t num_pages;
  size_t bigObjectSize;
  size_t bigObjectLimit;
  size_t size;
  void* pageArena;
  uintptr_t pageArenaEnd;
  uintptr_t pageArenaFinger;
  FreePage* freePage;
  size_t numFreeCommitedPages;
} HEAP;

SEXP* MarkStack;
size_t MSpos = 0;
size_t MSsize = 0;

int heapIsInitialized = 0;
void new_gc_initHeap() {
  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    SizeBucket* bucket = &HEAP.sizeBucket[i];
    bucket->to_bump = bucket->to_sweep = bucket->pages = NULL;
    bucket->num_pages = 0;
    Hashtable_init(&bucket->last_mark);
  }
  HEAP.page_limit = INITIAL_PAGE_LIMIT;
  HEAP.bigObjects = NULL;
  HEAP.bigObjectSize = 0;
  HEAP.bigObjectLimit = INITIAL_BIG_OBJ_LIMIT;
  HEAP.size = 0;
  HEAP.num_pages = 0;
  HEAP.numFreeCommitedPages = 0;

  size_t vmem = MAX_PAGES * PAGE_SIZE;
  HEAP.pageArena =
      mmap(NULL, vmem, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (HEAP.pageArena == MAP_FAILED)
    R_Suicide("Cannot setup heap");
  HEAP.pageArenaFinger = (uintptr_t)HEAP.pageArena;
  HEAP.pageArenaEnd = ((uintptr_t)HEAP.pageArena + vmem);
  size_t off = HEAP.pageArenaFinger % PAGE_SIZE;
  if (off != 0) {
    HEAP.pageArenaFinger += (PAGE_SIZE - off);
    HEAP.pageArenaEnd -= off;
  }
  CHECK(PTR2PAGE((void*)HEAP.pageArenaFinger) == (void*)HEAP.pageArenaFinger);
  HEAP.freePage = NULL;
  MarkStack = malloc(sizeof(SEXP) * INITIAL_MS_SIZE);
  MSsize = INITIAL_MS_SIZE;
  heapIsInitialized = 1;
}

inline SEXP alloc(size_t sz);

void* allocBigObj(size_t sexp_sz) {
  size_t sz = sizeof(BigObject) + sexp_sz;

  if (HEAP.bigObjectSize + sz > HEAP.bigObjectLimit)
    doGc(NUM_BUCKETS);

  if (HEAP.bigObjectSize + sz > HEAP.bigObjectLimit)
    HEAP.bigObjectLimit = (HEAP.bigObjectSize + sz) * HEAP_SLACK;

  void* data = malloc(sz);
  if (data == NULL)
    Rf_errorcall(R_NilValue, "error alloc");

  BigObject* obj = (BigObject*)data;
  // printf("Malloced big %p\n", obj);

  obj->mark = UNMARKED;
  obj->next = HEAP.bigObjects;
  obj->size = sz;

  HEAP.bigObjects = obj;
  HEAP.bigObjectSize += sz;

  INIT_NODE(obj->data);
  return obj->data;
}

void verifyPage(Page* page) {
  CHECK(page->next == NULL);
  uintptr_t pos = page->start;
  size_t last_idx = -1;
  while (pos != page->end) {
    CHECK(pos <= page->end);
    size_t idx = PTR2IDX((void*)pos);
    CHECK(idx != last_idx);
    last_idx = idx;
    CHECK(idx >= 0 && idx <= MAX_IDX);
    CHECK(pos < (uintptr_t)page + PAGE_SIZE);
    CHECK(PTR2PAGE((void*)pos) == page);
    pos += BUCKET_SIZE[page->bkt];
  }
  CHECK(page->end <= (uintptr_t)page + PAGE_SIZE);
}

Page* allocPage(unsigned bkt) {
  Page* page;
  if (HEAP.freePage != NULL) {
    FreePage* freelist = HEAP.freePage;
    page = freelist->finger;
    if (!freelist->commited) {
      int res = mprotect((void*)page, PAGE_SIZE, PROT_READ | PROT_WRITE);
      if (res != 0)
        R_Suicide("alloc page failed");
    }
    HEAP.freePage = HEAP.freePage->next;
    free(freelist);
  } else {
    page = (Page*)HEAP.pageArenaFinger;
    HEAP.pageArenaFinger += PAGE_SIZE;
    if (HEAP.pageArenaFinger >= HEAP.pageArenaEnd) {
      R_Suicide("Ran out of vmem");
    }
    int res = mprotect((void*)page, PAGE_SIZE, PROT_READ | PROT_WRITE);
    if (res != 0)
      R_Suicide("alloc page failed");
  }
  memset((void*)&page->mark, UNMARKED, MAX_IDX);
  page->next = NULL;
  page->prev = NULL;
  uintptr_t start = (uintptr_t)page->data;
  if (start % PAGE_IDX != 0)
    start += PAGE_IDX - (start % PAGE_IDX);
  page->start = page->sweep_end = start;
  page->alloc_finger = page->sweep_finger = page->start;

  uintptr_t end = (uintptr_t)page + PAGE_SIZE;
  size_t available = end - page->start;
  size_t tail = available % BUCKET_SIZE[bkt];
  end -= tail;
  page->end = end;
  page->split_page = 0;

  page->bkt = bkt;
  page->last_mark = UNMARKED;
  page->full = 0;
  page->available_nodes = available / BUCKET_SIZE[bkt];
  // printf("allocated a %d page %p from %p to %p\n", bkt, page, page->start,
  // page->end);
#ifdef GCDEBUG
  verifyPage(page);
#endif
  return page;
}

void growBucket(unsigned bkt) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  Page* page = allocPage(bkt);

  page->next = bucket->pages;
  if (bucket->pages)
    bucket->pages->prev = page;
  bucket->pages = page;
  bucket->to_bump = page;
  while (!Hashtable_add(bucket->last_mark, page, page->last_mark))
    Hashtable_grow(&bucket->last_mark);

  size_t available = page->end - page->start;

  HEAP.size += available;
  bucket->num_pages++;
  HEAP.num_pages++;
}

Page* deletePage(SizeBucket* bucket, Page* p) {
  HEAP.size -= p->end - p->start;
  CHECK(bucket->num_pages > 0);
  bucket->num_pages--;
  HEAP.num_pages--;
  if (bucket->to_bump == p)
    bucket->to_bump = NULL;
  if (bucket->to_sweep == p)
    bucket->to_sweep = p->next;
  Page* del = p;
  if (p->next)
    p->next->prev = p->prev;
  if (p->prev)
    p->prev->next = p->next;
  else
    bucket->pages = p->next;
  Page* next = p->next;
  FreePage* freelist = malloc(sizeof(FreePage));
  if (freelist == NULL)
    R_Suicide("int err");
  freelist->finger = del;
  freelist->commited = TRUE;
  freelist->next = HEAP.freePage;
  if (HEAP.numFreeCommitedPages >= FREE_PAGES_SLACK) {
    mprotect(del, PAGE_SIZE, PROT_NONE);
    freelist->commited = FALSE;
  }
  HEAP.freePage = freelist;
  return next;
}

void* findPageToSweep(SizeBucket* bucket) {
  Page* page = bucket->to_sweep->next;
  while (page != NULL) {
    if (!page->full) {
      page->sweep_finger = page->start;
      page->sweep_end = page->split_page != 0 ? page->split_page : page->end;
      page->split_page = 0;
      page->reclaimed_nodes = 0;
      // printf("Will now sweep a %d page %p from %p to %p\n", page->bkt, page,
      // page->start, page->sweep_end);
      break;
    }
    page = page->next;
  }
  bucket->to_sweep = page;
}

void* sweepAllocInBucket(unsigned bkt, SizeBucket* bucket);

void* slowAllocInBucket(unsigned bkt) {
  // No luck so far. If we are below the page limit
  // we can allocate more. Otherwise we need to do a gc.
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  if (HEAP.page_limit <= HEAP.num_pages) {
    doGc(bkt);
    // TODO: something a more sane...
    return sweepAllocInBucket(bkt, bucket);
  }

  if (HEAP.page_limit <= bucket->num_pages) {
    R_Suicide("fatal, run out of space");
  }

  growBucket(bkt);

  {
    Page* page = bucket->to_bump;
    void* res = (void*)page->alloc_finger;
    size_t i = PTR2IDX(res);
    CHECK(page->mark[i] == 0);
    page->alloc_finger += BUCKET_SIZE[bkt];
    return res;
  }
}

#define IDX2PTR(p, i) ((uintptr_t)(p) + ((i) << PAGE_IDX_BITS))

inline void* sweepAllocInBucketCellAligned(unsigned bkt, SizeBucket* bucket, size_t cells) {
  size_t sz = BUCKET_SIZE[bkt];

  // Lazy sweeping
  while (bucket->to_sweep != NULL) {
    Page* page = bucket->to_sweep;
    CHECK(sz >= PAGE_IDX);
    // page->end might overflow to the next page and produce idx 0, therefore
    // we get the idx of the prev cell and add 1. This is safe since the
    // first idx is > 0.
    size_t i = PTR2IDX(page->sweep_finger - PAGE_IDX) + 1;
    size_t l = PTR2IDX(page->sweep_end - PAGE_IDX) + 1;
    CHECK(IDX2PTR(page, PTR2IDX(page->start)) == page->start);
    CHECK(IDX2PTR(page, i) == page->sweep_finger);
    CHECK(IDX2PTR(page, i + cells) == page->sweep_finger + sz);
    CHECK(IDX2PTR(page, l) == page->sweep_end);
    for (; i < l; i += cells) {
      if (page->mark[i] < THE_MARK) {
        void* res = (void*)IDX2PTR(page, i);
        page->sweep_finger = IDX2PTR(page, i + cells);
        page->reclaimed_nodes++;
        return res;
      }
    }
    if ((double)page->reclaimed_nodes / (double)page->available_nodes <=
        PAGE_FULL_TRESHOLD)
      page->full = 1;
    page->sweep_finger = page->sweep_end;
    findPageToSweep(bucket);
  }

  return slowAllocInBucket(bkt);
}


inline void* sweepAllocInBucket(unsigned bkt, SizeBucket* bucket) {
  size_t sz = BUCKET_SIZE[bkt];

  // Lazy sweeping
  while (bucket->to_sweep != NULL) {
    Page* page = bucket->to_sweep;
    uintptr_t finger = page->sweep_finger;
    while (finger < page->sweep_end) {
      void* res = (void*)finger;
      size_t i = PTR2IDX(res);
      CHECK(i < MAX_IDX);
      finger += sz;
      if (page->mark[i] < THE_MARK) {
        page->sweep_finger = finger;
        page->reclaimed_nodes++;
        return res;
      }
    }
    if ((double)page->reclaimed_nodes / (double)page->available_nodes <=
        PAGE_FULL_TRESHOLD)
      page->full = 1;
    page->sweep_finger = page->sweep_end;
    findPageToSweep(bucket);
  }

  return slowAllocInBucket(bkt);
}

inline void* allocInBucket(unsigned bkt) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  // First try bump pointer alloc in the current page
  if (bucket->to_bump != NULL) {
    Page* page = bucket->to_bump;
    size_t next = page->alloc_finger + BUCKET_SIZE[bkt];
    if (next <= page->end) {
      void* res = (void*)page->alloc_finger;
      size_t i = PTR2IDX(res);
      CHECK((uintptr_t)res + BUCKET_SIZE[bkt] <= page->end);
      CHECK(PTR2PAGE(res) == page);
      CHECK(i > 0 && i < MAX_IDX);
      page->alloc_finger = next;
      INIT_NODE(res);
      return res;
    } else {
      bucket->to_bump = NULL;
      // printf("%d page %p is full\n", page->bkt, page);
    }
  }
  void* res;
  size_t cells;
  if ((cells = CELL_ALIGNED[bkt])) {
    res = sweepAllocInBucketCellAligned(bkt, bucket, cells);
  } else {
    res = sweepAllocInBucket(bkt, bucket);
  }
  INIT_NODE(res);
  return res;
}

inline SEXP alloc(size_t sz) {
  unsigned bkt = FIRST_GENERIC_BUCKET;
  while (bkt < NUM_BUCKETS && BUCKET_SIZE[bkt] < sz)
    ++bkt;
  if (bkt < NUM_BUCKETS) {
    SEXP res = (SEXP)allocInBucket(bkt);
    // printf("allo %p for %d in %d\n", res, sz, BUCKET_SIZE[bkt]);
    CHECK(!ISMARKED(res));
    return res;
  }
  return (SEXP)allocBigObj(sz);
}

#define intCHARSXP 73
SEXP new_gc_allocVector3_slow(SEXPTYPE type, R_xlen_t length);

SEXP inline new_gc_allocVector3(SEXPTYPE type,
                                R_xlen_t length,
                                R_allocator_t* allocator) {
  if (allocator != NULL)
    error(_("custom allocator not supported"));

  /* Handle some scalars directly to improve speed. */
  if (length == 1) {
    switch (type) {
      case REALSXP:
      case INTSXP:
      case LGLSXP: {
        SEXP s = allocInBucket(FIRST_GENERIC_BUCKET);
        ATTRIB(s) = R_NilValue;
        SET_TYPEOF(s, type);
        SET_SHORT_VEC_LENGTH(s, (R_len_t)length);  // is 1
        SET_SHORT_VEC_TRUELENGTH(s, 0);
        SET_NAMED(s, 0);
        INIT_REFCNT(s);
        return (s);
      }
    }
  }
  return new_gc_allocVector3_slow(type, length);
}

SEXP new_gc_allocVector3_slow(SEXPTYPE type, R_xlen_t length) {
  if (length > R_XLEN_T_MAX)
    error(_("vector is too large")); /**** put length into message */
  else if (length < 0)
    error(_("negative length vectors are not allowed"));

  size_t size = 0;

  /* number of vector cells to allocate */
  switch (type) {
    case NILSXP:
      return R_NilValue;
    case RAWSXP:
      size = BYTE2VEC(length);
      break;
    case CHARSXP:
      error("use of allocVector(CHARSXP ...) is defunct\n");
    case intCHARSXP:
      type = CHARSXP;
      size = BYTE2VEC(length + 1);
      break;
    case LGLSXP:
    case INTSXP:
      if (length > R_SIZE_T_MAX / sizeof(int))
        error(_("cannot allocate vector of length %d"), length);
      size = INT2VEC(length);
      break;
    case REALSXP:
      if (length > R_SIZE_T_MAX / sizeof(double))
        error(_("cannot allocate vector of length %d"), length);
      size = FLOAT2VEC(length);
      break;
    case CPLXSXP:
      if (length > R_SIZE_T_MAX / sizeof(Rcomplex))
        error(_("cannot allocate vector of length %d"), length);
      size = COMPLEX2VEC(length);
      break;
    case STRSXP:
    case EXPRSXP:
    case VECSXP:
      if (length > R_SIZE_T_MAX / sizeof(SEXP))
        error(_("cannot allocate vector of length %d"), length);
      size = PTR2VEC(length);
      break;
    case LANGSXP:
      if (length == 0)
        return R_NilValue;
#ifdef LONG_VECTOR_SUPPORT
      if (length > R_SHORT_LEN_MAX)
        error("invalid length for pairlist");
#endif
      {
        SEXP s = allocList((int)length);
        SET_TYPEOF(s, LANGSXP);
        return s;
      }
    case LISTSXP:
#ifdef LONG_VECTOR_SUPPORT
      if (length > R_SHORT_LEN_MAX)
        error("invalid length for pairlist");
#endif
      return allocList((int)length);
    default:
      error(_("invalid type/length (%s/%d) in vector allocation"),
            type2char(type),
            length);
  }

  R_size_t hdrsize = sizeof(SEXPREC_ALIGN);

#ifdef LONG_VECTOR_SUPPORT
  if (length > R_SHORT_LEN_MAX)
    hdrsize = sizeof(SEXPREC_ALIGN) + sizeof(R_long_vec_hdr_t);
#endif

  SEXP s = (SEXP)alloc(hdrsize + sizeof(VECREC) * size);

#ifdef LONG_VECTOR_SUPPORT
  if (length > R_SHORT_LEN_MAX) {
    s = (SEXP)(((char*)s) + sizeof(R_long_vec_hdr_t));
    SET_SHORT_VEC_LENGTH(s, R_LONG_VEC_TOKEN);
    SET_LONG_VEC_LENGTH(s, length);
    SET_LONG_VEC_TRUELENGTH(s, 0);
  } else {
    SET_SHORT_VEC_LENGTH(s, (R_len_t)length);
    SET_SHORT_VEC_TRUELENGTH(s, 0);
  }
#else
  SET_SHORT_VEC_LENGTH(s, (R_len_t)length);
  SET_SHORT_VEC_TRUELENGTH(s, 0);
#endif

  INIT_REFCNT(s);
  ATTRIB(s) = R_NilValue;
  SET_TYPEOF(s, type);
  SET_NAMED(s, 0);

  /* The following prevents disaster in the case */
  /* that an uninitialised string vector is marked */
  /* Direct assignment is OK since the node was just allocated and */
  /* so is at least as new as R_NilValue and R_BlankString */
  if (type == EXPRSXP || type == VECSXP) {
    SEXP* data = STRING_PTR(s);
    for (R_xlen_t i = 0; i < length; i++)
      data[i] = R_NilValue;
  } else if (type == STRSXP) {
    SEXP* data = STRING_PTR(s);
    for (R_xlen_t i = 0; i < length; i++)
      data[i] = R_BlankString;
  } else if (type == CHARSXP || type == intCHARSXP) {
    CHAR_RW(s)[length] = 0;
  }
  return s;
}

void heapStatistics() {
  printf("HEAP statistics after gc %d of gen %d: size %d + %d, pages %d / %d\n",
         gc_cnt,
         fullCollection,
         HEAP.size / 1024 / 1024,
         HEAP.bigObjectSize / 1024 / 1024,
         HEAP.num_pages,
         HEAP.page_limit);

  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    size_t available = 0;
    Page* p = HEAP.sizeBucket[i].pages;
    while (p != NULL) {
      available += p->available_nodes;
      p = p->next;
    }
    printf(" Bucket %d (%d) : pages %d, nodes %d\n",
           i,
           BUCKET_SIZE[i],
           HEAP.sizeBucket[i].num_pages,
           available);
  }
}

double pressure(unsigned bkt) {
  if (bkt == NUM_BUCKETS) {
    return (double)HEAP.bigObjectSize / (double)HEAP.bigObjectLimit;
  }
  return (double)(HEAP.num_pages) / (double)HEAP.page_limit;
}

void finish_sweep();
static void traceHeap();
void traceStack();
void free_unused_memory();
void PROCESS_NODE(SEXP);

#include <time.h>

double toMS(struct timespec* ts) {
  return (double)ts->tv_sec * 1000L + (double)ts->tv_nsec / 1000000.0;
}

size_t marked = 0;

SEXP intProtect[3] = {NULL, NULL, NULL};

inline void PROCESS_NODES();
inline void PUSH_NODE(SEXP);

void updatePageMark(Page* p) {
  Hashtable_set(HEAP.sizeBucket[p->bkt].last_mark, p, THE_MARK);
  p->last_mark = THE_MARK;
}

#define markIfUnmarked(s, what)                                        \
  if (ISNODE(s)) {                                                     \
    Page* p = PTR2PAGE(s);                                             \
    size_t i = PTR2IDX(s);                                             \
    if (p->mark[i] < THE_MARK) {                                       \
      if (p->last_mark < THE_MARK)                                     \
        updatePageMark(p);                                             \
      p->mark[i] = THE_MARK;                                           \
      { what; }                                                        \
    }                                                                  \
  } else {                                                             \
    BigObject* o = PTR2BIG(s);                                         \
    if (o->mark < THE_MARK) {                                          \
      o->mark = THE_MARK;                                              \
      { what; }                                                        \
    }                                                                  \
  }

void clear_marks();

void doGc(unsigned bkt) {
#ifdef GCPROF
  struct timespec time1, time2, time3, time4;
  marked = 0;
  clock_gettime(CLOCK_MONOTONIC, &time1);
#endif

  // clear mark bits
  if (fullCollection) {
    if (THE_MARK == 0xff) {
      clear_marks();
      THE_MARK = 1;
    } else {
      THE_MARK++;
    }
  }

#ifdef GCPROF
  clock_gettime(CLOCK_MONOTONIC, &time2);
#endif

  markIfUnmarked(R_NilValue, {});
  PROCESS_NODE(R_NilValue);
  if (intProtect[0]) {
    PUSH_NODE(intProtect[0]);
    intProtect[0] = NULL;
  }
  if (intProtect[1]) {
    PUSH_NODE(intProtect[1]);
    intProtect[1] = NULL;
  }
  if (intProtect[2]) {
    PUSH_NODE(intProtect[2]);
    intProtect[2] = NULL;
  }

  // traceStack();
  traceHeap();
  CHECK(MSpos == 0);

#ifdef GCPROF
  clock_gettime(CLOCK_MONOTONIC, &time3);
#endif

  free_unused_memory(bkt, fullCollection);
  gc_cnt++;
#if GCPROF
  if (gc_cnt % 10 == 0)
    heapStatistics();
#endif

  double p = pressure(bkt);
  if (p > HEAP_SLACK && fullCollection) {
    if (bkt == NUM_BUCKETS) {
      HEAP.bigObjectLimit *= GROW_RATE;
    } else {
      HEAP.page_limit *= GROW_RATE;
    }
  }

#ifdef GCPROF
  clock_gettime(CLOCK_MONOTONIC, &time4);
  printf(
      "Gc %d (%d) of gen %d : took %f to clear, %f to mark %d, %f to free, "
      "total %fms\n",
      gc_cnt,
      bkt,
      fullCollection,
      toMS(&time2) - toMS(&time1),
      toMS(&time3) - toMS(&time2),
      toMS(&time4) - toMS(&time3),
      toMS(&time4) - toMS(&time1),
      marked);
#endif
  fullCollection = p > FULL_COLLECTION_TRIGGER;
}

void clear_marks() {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];

    size_t ht_size = bucket->last_mark->size * bucket->last_mark->bucket_size;
    for (size_t i = 0; i < ht_size; ++i) {
      HashtableEntry e = bucket->last_mark->data[i];
      if (e.page != NULL) {
        Page* p = e.page;
        CHECK(p->sweep_finger <= p->sweep_end &&
              p->sweep_end <= p->alloc_finger);
        p->full = 0;
        p->last_mark = UNMARKED;
        bucket->last_mark->data[i].mark = UNMARKED;
        p->sweep_finger = p->sweep_end;
        memset(&p->mark, UNMARKED, MAX_IDX);
      }
    }
  }
  BigObject* o = HEAP.bigObjects;
  while (o != NULL) {
    o->mark = UNMARKED;
    o = o->next;
  }
}

void free_unused_memory(unsigned bkt, Rboolean all) {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];

    size_t ht_size = bucket->last_mark->size * bucket->last_mark->bucket_size;
    for (size_t i = 0; i < ht_size; ++i) {
      HashtableEntry e = bucket->last_mark->data[i];
      if (e.page != NULL) {
        if (e.mark < THE_MARK) {
          CHECK(e.mark == e.page->last_mark);
          Hashtable_remove_el(bucket->last_mark, i);
          deletePage(bucket, e.page);
        }
      }
    }

    bucket->to_sweep = bucket->pages;
    // If a page has still some bump-alloc space left we need to make sure not
    // to lazy-sweep into the this part of the page during this gc cycle.
    if (bucket->to_bump)
      bucket->to_bump->split_page = bucket->to_bump->alloc_finger;
  }

  if (bkt != NUM_BUCKETS && !all)
    return;

  BigObject* o = HEAP.bigObjects;
  BigObject** prevptr = &HEAP.bigObjects;
  while (o != NULL) {
    if (o->mark < THE_MARK) {
      HEAP.bigObjectSize -= o->size;
      void* del = o;
      size_t sz = o->size;
      *prevptr = o->next;
      o = o->next;
      ON_DEBUG(memset(del, 0xd0, sz));
      free(del);
    } else {
      prevptr = &o->next;
      o = o->next;
    }
  }
}

inline Rboolean NODE_IS_MARKED(SEXP s) {
  return ISMARKED(s);
}

inline void FORWARD_NODE(SEXP s) {
  if (s == NULL || s == R_NilValue)
    return;
  markIfUnmarked(s, {
    PROCESS_NODE(s);
#ifdef GCPROF
    ++marked;
#endif
  });
  if (MSpos > MS_TRIGGER)
    PROCESS_NODES();
}

inline void PROCESS_NODES() {
  while (MSpos > 0) {
    PROCESS_NODE(MarkStack[--MSpos]);
  }
}

void growMarkStack() {
  size_t old_size = MSsize*sizeof(SEXP);
  MSsize *= 1.5;
  size_t new_size = MSsize*sizeof(SEXP);
  SEXP* newMS = malloc(new_size);
  memcpy(newMS, MarkStack, old_size);
  free(MarkStack);
  MarkStack = newMS;
}

inline void __attribute__((always_inline)) PUSH_NODE(SEXP s) {
  if (s == NULL || s == R_NilValue)
    return;
  if (MSpos >= MSsize) {
    growMarkStack();
  }
  markIfUnmarked(s, {
#ifdef GCPROF
    ++marked;
#endif
    MarkStack[MSpos++] = s;
  });
}

#define MARK_OLD(s)               \
  if ((s)->sxpinfo.old != 1)      \
    (s)->sxpinfo.old = 1

inline void PROCESS_NODE(SEXP cur) {
  SEXP attrib = ATTRIB(cur);
  switch (TYPEOF(cur)) {
    case CHARSXP:
      // not marked old, see ATTRIB_WRITE_BARRIER
      if (attrib != R_NilValue && TYPEOF(attrib) != CHARSXP)
        PUSH_NODE(ATTRIB(cur));
      break;
    case NILSXP:
    case BUILTINSXP:
    case SPECIALSXP:
    case LGLSXP:
    case INTSXP:
    case REALSXP:
    case CPLXSXP:
    case WEAKREFSXP:
    case RAWSXP:
    case S4SXP:
      // not marked old, see ATTRIB_WRITE_BARRIER
      if (attrib != R_NilValue)
        PUSH_NODE(ATTRIB(cur));
      break;
    case STRSXP:
    case EXPRSXP:
    case VECSXP:
      MARK_OLD(cur);
      if (attrib != R_NilValue)
        PUSH_NODE(ATTRIB(cur));
      {
        R_xlen_t i;
        for (i = 0; i < XLENGTH(cur); i++)
          PUSH_NODE(VECTOR_ELT(cur, i));
      }
      break;
    case ENVSXP:
      MARK_OLD(cur);
      if (attrib != R_NilValue)
        PUSH_NODE(ATTRIB(cur));
      PUSH_NODE(FRAME(cur));
      PUSH_NODE(ENCLOS(cur));
      PUSH_NODE(HASHTAB(cur));
      break;
    case CLOSXP:
    case PROMSXP:
    case LISTSXP:
    case LANGSXP:
    case DOTSXP:
    case SYMSXP:
    case BCODESXP:
      MARK_OLD(cur);
      if (attrib != R_NilValue)
        PUSH_NODE(ATTRIB(cur));
      PUSH_NODE(TAG(cur));
      PUSH_NODE(CAR(cur));
      PUSH_NODE(CDR(cur));
      break;
    case EXTPTRSXP:
      MARK_OLD(cur);
      if (attrib != R_NilValue)
        PUSH_NODE(ATTRIB(cur));
      PUSH_NODE(EXTPTR_PROT(cur));
      PUSH_NODE(EXTPTR_TAG(cur));
      break;
    default:
      CHECK(0);
  }
}

void write_barrier_trigger(SEXP x, SEXP y) {
  // To avoid the barrier triggering multiple times we clear the old bit for as
  // long as the node is in the mark queue.
  x->sxpinfo.old = 0;
  *GETMARK(x) = UNMARKED;
  PUSH_NODE(x);
  if (MSpos > WRITE_BARRIER_MS_TRIGGER)
    PROCESS_NODES();
}

#define WRITE_BARRIER(x, y)                                       \
  if (!fullCollection && (x)->sxpinfo.old && !(y)->sxpinfo.old) { \
    write_barrier_trigger(x, y);                                  \
  }

void ATTRIB_WRITE_BARRIER(SEXP x, SEXP y) {
  switch (TYPEOF(x)) {
  case CHARSXP:
  case NILSXP:
  case BUILTINSXP:
  case SPECIALSXP:
  case LGLSXP:
  case INTSXP:
  case REALSXP:
  case CPLXSXP:
  case WEAKREFSXP:
  case RAWSXP:
  case S4SXP:
    // SEXPs with just the attrib pointer are not marked old for efficiency
    // reasons. That means that we need a more expensive write barrier.
    if (!fullCollection && NODE_IS_MARKED(x) && !NODE_IS_MARKED(y)) {
      write_barrier_trigger(x, y);
    }
    break;
  case STRSXP:
  case EXPRSXP:
  case VECSXP:
  case ENVSXP:
  case CLOSXP:
  case PROMSXP:
  case LISTSXP:
  case LANGSXP:
  case DOTSXP:
  case SYMSXP:
  case BCODESXP:
  case EXTPTRSXP:
    WRITE_BARRIER(x, y);
    break;
  default:
    CHECK(0);
  }
}

#define GET_FREE_NODE(s)                      \
  do {                                        \
    (s) = allocInBucket(GENERIC_SEXP_BUCKET); \
  } while (0)

#define ALLOC_SEXP(s, t)                      \
  do {                                        \
    (s) = allocInBucket(GENERIC_SEXP_BUCKET); \
  } while (0)

#define ALLOC_CONS(s, p1, p2)         \
  do {                                \
    intProtect[0] = (p1);             \
    intProtect[1] = (p2);             \
    (s) = allocInBucket(CONS_BUCKET); \
  } while (0)

#define ALLOC_ENV(s, p1, p2, p3)     \
  do {                               \
    intProtect[0] = (p1);            \
    intProtect[1] = (p2);            \
    intProtect[2] = (p3);            \
    (s) = allocInBucket(ENV_BUCKET); \
  } while (0)

#define ALLOC_PROM(s, p1, p2)         \
  do {                                \
    intProtect[0] = (p1);             \
    intProtect[1] = (p2);             \
    (s) = allocInBucket(PROM_BUCKET); \
  } while (0)
