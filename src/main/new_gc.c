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
#include <Rmath.h> // R_pow_di
#include <Print.h> // R_print

#ifdef COMPUTE_REFCNT_VALUES
#define INIT_REFCNT(x) do {			\
	SEXP __x__ = (x);			\
	SET_REFCNT(__x__, 0);			\
	SET_TRACKREFS(__x__, TRUE);		\
    } while (0)
#else
#define INIT_REFCNT(x) do {} while (0)
#endif


#define PAGE_SIZE      0x4000
#define PAGE_IDX       32
#define PAGE_IDX_BITS  5
#define PAGE_MASK      0x3fff
#define MAX_IDX (PAGE_SIZE/PAGE_IDX)

#define UNMARKED 0
#define STICKY_MARK 0xff
static uint8_t THE_MARK = 1;

// #define GCDEBUG
#ifdef GCDEBUG
#define CHECK(exp) if(!(exp)) asm("int3")
#define ON_DEBUG(exp) exp
#else
#define CHECK(exp) {}
#define ON_DEBUG {}
#endif

static size_t gc_cnt = 0;
static Rboolean fullCollection = FALSE;

#define BIG_OBJ_ALIGN 64
#define CONS_BUCKET 0
#define ENV_BUCKET 1
#define PROM_BUCKET 2
#define GENERIC_SEXP_BUCKET 3
#define NUM_BUCKETS 23
#define FIRST_GENERIC_BUCKET 4

  static size_t BUCKET_SIZE[NUM_BUCKETS] = {40, 40, 40, 40, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 128, 160, 192, 256, 320, 512, 768, 1024, 1290};
  static size_t INITIAL_PAGE_LIMIT = 500;
  static size_t INITIAL_BIG_OBJ_LIMIT = 32 * 1024 * 1024;
  static double PAGE_FULL_TRESHOLD = 0.01;
  static double GROW_RATE = 1.1;

  static inline size_t roundUp(size_t bs, size_t cs) {
    size_t res = bs / cs;
    if (res * cs >= bs)
      return res;
    return res+1;
  }

#pragma pack(push, 1)
  typedef struct Page {
    uint8_t mark[MAX_IDX];
    unsigned bkt  : 8;
    unsigned live : 1;
    unsigned old  : 1;
    unsigned full : 1;
    struct Page* next;
    uintptr_t end;
    uintptr_t finger;
    uintptr_t sweep_finger;
    uintptr_t sweep_end;
    size_t available_nodes;
    size_t reclaimed_nodes;
    char data[];
  } Page;

  typedef struct BigObject {
    uint8_t mark;
    struct BigObject* next;
    size_t size;
    char data[];
  } BigObject;
#pragma pack(pop)

#define PTR2PAGE(ptr) ((Page*)((uintptr_t)(ptr) & ~PAGE_MASK))
#define PTR2IDX(ptr) (((uintptr_t)(ptr) & PAGE_MASK) >> PAGE_IDX_BITS)
#define PTR2BIG(ptr) ((BigObject*)((uintptr_t)(ptr) - sizeof(BigObject)))
#define ISBIG(s, info) (((uintptr_t)s-sizeof(BigObject)) % BIG_OBJ_ALIGN == 0 && (info).big)
// #define ISBIG(s, info) ((info).big)
#define ISMARKED(s) (ISBIG(s,(s)->sxpinfo) \
    ? PTR2BIG(s)->mark >= THE_MARK \
    : PTR2PAGE(s)->mark[PTR2IDX(s)] >= THE_MARK)
#define ISOLD(s) (ISBIG(s,(s)->sxpinfo) \
    ? PTR2BIG(s)->mark == STICKY_MARK \
    : PTR2PAGE(s)->mark[PTR2IDX(s)] == STICKY_MARK)

  void verifyPage(Page* page) {
    CHECK(page->next == NULL);
    for (size_t i = PTR2IDX((SEXP)page->data); i < PTR2IDX((void*)page->end); ++i) {
      CHECK((void*)&page->mark[i] >= (void*)page &&
          (void*)&page->mark[i] < (void*)page->finger);
    }
    uintptr_t pos = page->finger;
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

  static void doGc(unsigned);
  Page* allocPage(unsigned bkt) {
    void* data;
    int res = posix_memalign(&data, PAGE_SIZE, PAGE_SIZE);
    if (res != 0)
      Rf_errorcall(R_NilValue, "error alloc");
    ON_DEBUG(memset(data, 0, PAGE_SIZE));
    Page* page = (Page*)data;
    memset(&page->mark, UNMARKED, MAX_IDX);
    // CHECK((uintptr_t)page->data % PAGE_IDX == 0);
    page->next = NULL;
    page->finger = (uintptr_t)page->data;
    page->end = (uintptr_t)page + PAGE_SIZE;
    size_t available = page->end - page->finger;
    size_t tail = available % BUCKET_SIZE[bkt];
    page->end -= tail;
    page->bkt = bkt;
    page->live = 0;
    page->old = 0;
    page->full = 0;
  page->available_nodes = available / BUCKET_SIZE[bkt];
  page->sweep_finger = page->sweep_end = (uintptr_t)page->data;
  // printf("allocated a %d page %p from %p to %p\n", bkt, page, page->finger, page->end);
  verifyPage(page);
  return page;
}

typedef struct SizeBucket {
  Page* cur;
  Page* pages;
  Page* next_to_sweep;
  size_t num_pages;
} SizeBucket;

struct {
  SizeBucket sizeBucket[NUM_BUCKETS];
  BigObject* bigObjects;
  size_t page_limit;
  size_t num_pages;
  size_t bigObjectSize;
  size_t bigObjectLimit;
  size_t size;
} HEAP;

static int heapIsInitialized = 0;
static void new_gc_initHeap() {
  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    SizeBucket* bucket = &HEAP.sizeBucket[i];
    bucket->pages = NULL;
    bucket->cur = NULL;
    bucket->next_to_sweep = NULL;
    bucket->num_pages = 0;
  }
  HEAP.page_limit = INITIAL_PAGE_LIMIT;
  HEAP.bigObjects = NULL;
  HEAP.bigObjectSize = 0;
  HEAP.bigObjectLimit = INITIAL_BIG_OBJ_LIMIT;
  HEAP.size = 0;
  HEAP.num_pages = 0;
  heapIsInitialized = 1;
}

SEXP alloc(size_t sz);

static void* allocBigObj(size_t sexp_sz) {
  size_t sz = sizeof(BigObject) + sexp_sz;

  if (HEAP.bigObjectSize + sz > HEAP.bigObjectLimit)
    doGc(NUM_BUCKETS);

  void* data;
  int res = posix_memalign(&data, BIG_OBJ_ALIGN, sz);
  if (res != 0)
    Rf_errorcall(R_NilValue, "error alloc");

  BigObject* obj = (BigObject*)data;
  ON_DEBUG(memset(obj, 0, sz));
  // printf("Malloced big %p\n", obj);

  obj->mark = UNMARKED;
  obj->next = HEAP.bigObjects;
  obj->size = sz;

  HEAP.bigObjects = obj;
  HEAP.bigObjectSize += sz;

  return obj->data;
}

static void growBucket(unsigned bkt) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  Page* page = allocPage(bkt);

  page->next = bucket->pages;
  bucket->pages = page;
  bucket->cur = page;

  size_t available = page->end - page->finger;

  HEAP.size += available;
  bucket->num_pages++;
  HEAP.num_pages++;
}

static void* findPageToSweep(SizeBucket* bucket) {
  Page* page = bucket->next_to_sweep;
  while (page != NULL) {
    CHECK(page->sweep_finger <= page->sweep_end);
    if (page->sweep_finger <= page->sweep_end) {
      if (!page->full)
        break;
    }
    page = page->next;
  }
  bucket->next_to_sweep = page == NULL ? NULL : page->next;
  bucket->cur = page;
}

static void* sweepAllocInBucket(unsigned bkt) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];

  if (bucket->cur == NULL)
    findPageToSweep(bucket);

  // Lazy sweeping
  while (bucket->cur != NULL) {
    Page* page = bucket->cur;
    uintptr_t finger = page->sweep_finger;
    while (finger < page->sweep_end) {
      void* res = (void*)finger;
      size_t i = PTR2IDX(res);
      CHECK(i < MAX_IDX);
      finger += BUCKET_SIZE[bkt];
      if (page->mark[i] < THE_MARK) {
        page->mark[i] = UNMARKED;
        page->sweep_finger = finger;
        page->reclaimed_nodes++;
        ON_DEBUG(memset(res, 0, BUCKET_SIZE[bkt]));
        return res;
      }
    }
    if ((double)page->reclaimed_nodes / (double)page->available_nodes < PAGE_FULL_TRESHOLD)
      page->full = 1;
    page->sweep_finger = page->sweep_end;
    findPageToSweep(bucket);
  }
  return NULL;
}

static inline void* allocInBucket(unsigned bkt);
static void* slowAllocInBucket(unsigned bkt) {
  {
    // Try to lazy sweep some free space
    void* res = sweepAllocInBucket(bkt);
    if (res)
      return res;
  }

  // No luck so far. If we are below the page limit
  // we can allocate more. Otherwise we need to do a gc.
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  if (HEAP.page_limit <= HEAP.num_pages) {
    doGc(bkt);
    // TODO: something a more sane...
    return allocInBucket(bkt);
  }

  if (HEAP.page_limit <= bucket->num_pages) {
    puts("fatal, run out of space");
    exit(2);
  }

  growBucket(bkt);

  {
    Page* page = bucket->cur;
    void* res = (void*)page->finger;
    size_t i = PTR2IDX(res);
    CHECK(page->mark[i] == 0);
    page->finger += BUCKET_SIZE[bkt];
    return res;
  }
}

static __attribute__ ((always_inline)) void* allocInBucket(unsigned bkt) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  Page* page = bucket->cur;
  // First try bump pointer alloc in the current page
  if (page != NULL) {
    size_t next = page->finger + BUCKET_SIZE[bkt];
    if (next <= page->end) {
      void* res = (void*)page->finger;
      size_t i = PTR2IDX(res);
      CHECK((uintptr_t)res + BUCKET_SIZE[bkt] <= page->end);
      CHECK(PTR2PAGE(res) == page);
      CHECK(i > 0 && i < MAX_IDX);
      page->finger = next;
      return res;
    }
  }
  CHECK(page == NULL || page->finger == page->end);
  return slowAllocInBucket(bkt);
}

SEXP alloc(size_t sz) {
  unsigned bkt = FIRST_GENERIC_BUCKET;
  while (bkt < NUM_BUCKETS && BUCKET_SIZE[bkt] < sz) ++bkt;
  if (bkt < NUM_BUCKETS) {
    SEXP res = (SEXP)allocInBucket(bkt);
    // printf("allo %p for %d in %d\n", res, sz, BUCKET_SIZE[bkt]);
    CHECK(!ISMARKED(res));
    memset(res, 0, sizeof(struct sxpinfo_struct));
    res->sxpinfo.big = 0;
    return res;
  }
  SEXP res = (SEXP) allocBigObj(sz);
  memset(res, 0, sizeof(struct sxpinfo_struct));
  res->sxpinfo.big = 1;
  return res;
}

#define intCHARSXP 73
SEXP new_gc_allocVector3(SEXPTYPE type, R_xlen_t length, R_allocator_t *allocator) {
  if (allocator != NULL)
    error(_("custom allocator not supported"));
  if (length > R_XLEN_T_MAX)
    error(_("vector is too large")); /**** put length into message */
  else if (length < 0 )
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
    if(length == 0) return R_NilValue;
#ifdef LONG_VECTOR_SUPPORT
    if (length > R_SHORT_LEN_MAX) error("invalid length for pairlist");
#endif
    {
      SEXP s = allocList((int) length);
      SET_TYPEOF(s, LANGSXP);
      return s;
    }
  case LISTSXP:
#ifdef LONG_VECTOR_SUPPORT
    if (length > R_SHORT_LEN_MAX) error("invalid length for pairlist");
#endif
    return allocList((int) length);
  default:
    error(_("invalid type/length (%s/%d) in vector allocation"),
          type2char(type), length);
  }

  R_size_t hdrsize = sizeof(SEXPREC_ALIGN);

#ifdef LONG_VECTOR_SUPPORT
  if (length > R_SHORT_LEN_MAX)
    hdrsize = sizeof(SEXPREC_ALIGN) + sizeof(R_long_vec_hdr_t);
#endif

  SEXP s = (SEXP)alloc(hdrsize + sizeof(VECREC)*size);

#ifdef LONG_VECTOR_SUPPORT
  if (length > R_SHORT_LEN_MAX) {
    s = (SEXP) (((char *) s) + sizeof(R_long_vec_hdr_t));
    SET_SHORT_VEC_LENGTH(s, R_LONG_VEC_TOKEN);
    SET_LONG_VEC_LENGTH(s, length);
    SET_LONG_VEC_TRUELENGTH(s, 0);
  } else {
    SET_SHORT_VEC_LENGTH(s, (R_len_t) length);
    SET_SHORT_VEC_TRUELENGTH(s, 0);
  }
#else
  SET_SHORT_VEC_LENGTH(s, (R_len_t) length);
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
    SEXP *data = STRING_PTR(s);
    for (R_xlen_t i = 0; i < length; i++)
      data[i] = R_NilValue;
  } else if(type == STRSXP) {
    SEXP *data = STRING_PTR(s);
    for (R_xlen_t i = 0; i < length; i++)
      data[i] = R_BlankString;
  } else if (type == CHARSXP || type == intCHARSXP) {
    CHAR_RW(s)[length] = 0;
  }
  return s;
}

#pragma pack(push, 1)
#define MS_SIZE 40000
typedef struct MSEntry {
  SEXP entry;
  uint8_t mark;
  struct sxpinfo_struct info;
} MSEntry;
static MSEntry MarkStack[MS_SIZE+2];
static size_t MSpos = 0;
#pragma pack(pop)

static void heapStatistics() {
  printf("HEAP statistics after gc %d of gen %d: size %d, pages %d / %d\n",
      gc_cnt,
      fullCollection,
      HEAP.size / 1024 / 1024,
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
        i, BUCKET_SIZE[i],
        HEAP.sizeBucket[i].num_pages,
        available);
  }
}


static double pressure(unsigned bkt) {
  if (bkt == NUM_BUCKETS) {
    return (double)HEAP.bigObjectSize / (double)HEAP.bigObjectLimit;
  }
  SizeBucket* b = &HEAP.sizeBucket[bkt];
  return (double)HEAP.num_pages / (double)HEAP.page_limit;
}

static void finish_sweep();
static void traceHeap();
static void traceStack();
static void free_unused_memory();
static void PROCESS_NODE(SEXP, uint8_t, struct sxpinfo_struct);

#include <time.h>

static double toMS(struct timespec* ts) {
  return (double)ts->tv_sec * 1000L + (double)ts->tv_nsec / 1000000.0;
}

size_t marked = 0;

static SEXP intProtect[3] = {NULL, NULL, NULL};

static void PROCESS_NODES();
static void PUSH_NODE(SEXP, uint8_t);

// #define GCPROF 1

static Page* lastPage = NULL;
static inline __attribute__ ((always_inline)) uint8_t markIfUnmarked(SEXP s, uint8_t mark, struct sxpinfo_struct info) {
  if (!ISBIG(s, info)) {
    Page* p = PTR2PAGE(s);
    size_t i = PTR2IDX(s);
    if (p->mark[i] < mark) {
#ifdef GCPROF
      ++marked;
#endif
      if (p->live == 0)
        p->live = 1;
      if (p->mark[i] == UNMARKED) {
        p->mark[i] = mark;
        return mark;
      } else {
        p->mark[i] = STICKY_MARK;
        p->old = 1;
        return STICKY_MARK;
      }
    }
    return FALSE;
  }

  BigObject* o = PTR2BIG(s);
  if (o->mark < mark) {
    if (o->mark == UNMARKED) {
      o->mark = mark;
      return mark;
    } else {
      o->mark = STICKY_MARK;
      return STICKY_MARK;
    }
  }
  return FALSE;
}


static void clear_marks(Rboolean full);

void static doGc(unsigned bkt) {
#ifdef GCPROF
  struct timespec start;
  struct timespec end;
  marked = 0;
  clock_gettime(CLOCK_MONOTONIC, &start);
#endif

  // clear mark bits
  if (fullCollection) {
    clear_marks(TRUE);
    THE_MARK = 1;
  } else {
    if (THE_MARK == STICKY_MARK-1) {
      clear_marks(FALSE);
      THE_MARK = 1;
    } else {
      THE_MARK++;
    }
  }

  markIfUnmarked(R_NilValue, STICKY_MARK, R_NilValue->sxpinfo);
  PROCESS_NODE(R_NilValue, STICKY_MARK, R_NilValue->sxpinfo);
  if (intProtect[0]) {PUSH_NODE(intProtect[0], THE_MARK); intProtect[0] = NULL;}
  if (intProtect[1]) {PUSH_NODE(intProtect[1], THE_MARK); intProtect[1] = NULL;}
  if (intProtect[2]) {PUSH_NODE(intProtect[2], THE_MARK); intProtect[2] = NULL;}

  // traceStack();
  traceHeap();
  CHECK(MSpos == 0);

  free_unused_memory();

  gc_cnt++;
#if GCPROF
  if (gc_cnt % 10 == 0)
    heapStatistics();
#endif

  double p = pressure(bkt);
  if (p > 0.9 && fullCollection) {
    if (bkt == NUM_BUCKETS) {
      HEAP.bigObjectLimit *= GROW_RATE;
    } else {
      HEAP.page_limit *= GROW_RATE;
    }
  }
#ifdef GCPROF
  clock_gettime(CLOCK_MONOTONIC, &end);
  printf("Gc %d (%d) of gen %d took %f to mark %d\n", gc_cnt, bkt, fullCollection, toMS(&end)-toMS(&start), marked);
#endif
  fullCollection = p > 0.95;
}

static void clear_marks(Rboolean full) {
  if (full) {
    for (size_t s = 0; s < NUM_BUCKETS; ++s) {
      SizeBucket* bucket = &HEAP.sizeBucket[s];
      Page* p = bucket->pages;
      while (p != NULL) {
        CHECK(p->sweep_finger <= p->sweep_end && p->sweep_end <= p->finger);
        p->full = 0;
        p->sweep_finger = p->sweep_end;
        memset(&p->mark, UNMARKED, MAX_IDX);
        p = p->next;
      }
    }
    BigObject* o = HEAP.bigObjects;
    while (o != NULL) {
      o->mark = UNMARKED;
      o = o->next;
    }
  } else {
    for (size_t s = 0; s < NUM_BUCKETS; ++s) {
      SizeBucket* bucket = &HEAP.sizeBucket[s];
      Page* p = bucket->pages;
      while (p != NULL) {
        CHECK(p->sweep_finger <= p->sweep_end && p->sweep_end <= p->finger);
        uintptr_t finger = p->sweep_finger;
        while (finger < p->sweep_end) {
          size_t i = PTR2IDX((void*)finger);
          if (p->mark[i] != STICKY_MARK)
            p->mark[i] = UNMARKED;
          finger += BUCKET_SIZE[s];
        }
        p->sweep_finger = p->sweep_end;
        p = p->next;
      }
    }
    BigObject* o = HEAP.bigObjects;
    while (o != NULL) {
      if (o->mark != STICKY_MARK)
        o->mark = UNMARKED;
      o = o->next;
    }
  }
}

static void findPageToBump(SizeBucket* bucket) {
  bucket->cur = NULL;
  Page* page = bucket->pages;
  while (page != NULL) {
    CHECK(page->sweep_finger <= page->sweep_end &&
        page->sweep_end <= page->finger && page->finger <= page->end);
    if (page->finger < page->end) {
      // There should only ever be one page with free bump space
      CHECK(bucket->cur == NULL);
      bucket->cur = page;
#ifndef GCDEBUG
      return;
#endif
    }
    page = page->next;
  }
}

static void free_unused_memory() {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];
    Page* p = bucket->pages;
    Page** prevptr = &bucket->pages;

    while (p != NULL) {
      // gen of page = gen of oldest object.
      // liveness of page only valid if all its nodes where traced
      if ((p->old == 0 || fullCollection) && p->live == 0) {
        HEAP.size -= p->end - p->finger;
        CHECK(bucket->num_pages > 0);
        bucket->num_pages--;
        HEAP.num_pages--;
        if (bucket->cur == p)
          bucket->cur = NULL;
        void * del = p;
        *prevptr = p->next;
        p = p->next;
        ON_DEBUG(memset(del, 0xde, PAGE_SIZE));
        free(del);
      } else {
        // Set up the page for lazy sweeping
        if (fullCollection)
          p->live = 0;
        p->reclaimed_nodes = 0;
        p->sweep_finger = (uintptr_t)p->data;
        p->sweep_end = p->finger;
        prevptr = &p->next;
        p = p->next;
      }
    }

    bucket->next_to_sweep = bucket->pages;
    findPageToBump(bucket);
  }

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

# define HAS_GENUINE_ATTRIB(x) \
    (ATTRIB(x) != R_NilValue && \
     (TYPEOF(x) != CHARSXP || TYPEOF(ATTRIB(x)) != CHARSXP))

static inline Rboolean NODE_IS_MARKED(SEXP s) {
  return ISMARKED(s);
}

static inline void FORWARD_NODE(SEXP s) {
  if (s == NULL || s == R_NilValue) return;
  uint8_t m;
  struct sxpinfo_struct info = s->sxpinfo;
  if ((m = markIfUnmarked(s, THE_MARK, info))) {
    PROCESS_NODE(s, m, info);
  }
  //PROCESS_NODES();
}

static inline void PROCESS_NODES() {
  while (MSpos > 0) {
    MSEntry e = MarkStack[--MSpos];
  uint8_t m;
    PROCESS_NODE(e.entry, e.mark, e.info);
  }
}

static inline __attribute__((always_inline)) void PUSH_NODE(SEXP s, uint8_t mark) {
  if (s == NULL || s == R_NilValue) return;
  if (MSpos >= MS_SIZE) {
    puts("mstack overflow");
    exit(2);
  }
  uint8_t m;
  struct sxpinfo_struct info = s->sxpinfo;
  if ((m = markIfUnmarked(s, mark, info))) {
    MSEntry e = {s, m, info};
    MarkStack[MSpos++] = e;
  }
}

static inline __attribute__ ((always_inline)) void PROCESS_NODE(SEXP cur, uint8_t mark, struct sxpinfo_struct info) {
  SEXP attrib = ATTRIB(cur);
  switch (info.type) {
  case CHARSXP:
    if (attrib != R_NilValue && TYPEOF(attrib) != CHARSXP)
      PUSH_NODE(ATTRIB(cur), mark);
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
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur), mark);
    break;
  case STRSXP:
  case EXPRSXP:
  case VECSXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur), mark);
    {
      R_xlen_t i;
      for (i = 0; i < XLENGTH(cur); i++)
        PUSH_NODE(VECTOR_ELT(cur, i), mark);
    }
    break;
  case ENVSXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur), mark);
    PUSH_NODE(FRAME(cur), mark);
    PUSH_NODE(ENCLOS(cur), mark);
    PUSH_NODE(HASHTAB(cur), mark);
    break;
  case CLOSXP:
  case PROMSXP:
  case LISTSXP:
  case LANGSXP:
  case DOTSXP:
  case SYMSXP:
  case BCODESXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur), mark);
    PUSH_NODE(TAG(cur), mark);
    PUSH_NODE(CAR(cur), mark);
    PUSH_NODE(CDR(cur), mark);
    break;
  case EXTPTRSXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur), mark);
    PUSH_NODE(EXTPTR_PROT(cur), mark);
    PUSH_NODE(EXTPTR_TAG(cur), mark);
    break;
  default:
    CHECK(0);
  }
}

#define CHECK_OLD_TO_NEW(x, y) \
  if (!fullCollection) { \
    if (ISOLD(x) && !ISOLD(y)) { \
      PUSH_NODE(y, STICKY_MARK); \
      PROCESS_NODES(); \
    } \
  }

#define GET_FREE_NODE(s) do { \
  (s) = allocInBucket(GENERIC_SEXP_BUCKET); \
} while(0)

#define ALLOC_SEXP(s, t) do { \
  (s) = allocInBucket(GENERIC_SEXP_BUCKET); \
} while(0)

#define ALLOC_CONS(s, p1, p2) do { \
  intProtect[0] = (p1); \
  intProtect[1] = (p2); \
  (s) = allocInBucket(CONS_BUCKET); \
} while(0)

#define ALLOC_ENV(s, p1, p2, p3) do { \
  intProtect[0] = (p1); \
  intProtect[1] = (p2); \
  intProtect[2] = (p3); \
  (s) = allocInBucket(ENV_BUCKET); \
} while(0)

#define ALLOC_PROM(s, p1, p2) do { \
  intProtect[0] = (p1); \
  intProtect[1] = (p2); \
  (s) = allocInBucket(PROM_BUCKET); \
} while(0)
