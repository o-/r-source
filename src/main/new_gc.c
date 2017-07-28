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
#define MARK_BLACK 1
#define MARK_WHITE 0

// #define GCDEBUG
#ifdef GCDEBUG
#define CHECK(exp) if(!(exp)) asm("int3")
#define ON_DEBUG(exp) exp
#else
#define CHECK(exp) {}
#define ON_DEBUG {}
#endif

typedef struct Hashtable {
  size_t size;
  size_t bucket_size;
  void* data[];
} Hashtable;

static void Hashtable_init(Hashtable** ht) {
  size_t size = 64;
  size_t bucket_size = 16;

  size_t sz = sizeof(Hashtable) + size*bucket_size*sizeof(void*);
  Hashtable* h = malloc(sz);
  if (h == NULL) exit(1);
  memset(h, 0, sz);
  h->size = size;
  h->bucket_size = bucket_size;
  *ht = h;
}

static Rboolean Hashtable_add(Hashtable* ht, void* p);
static void Hashtable_grow(Hashtable** ht) {
  Hashtable* old = *ht;
  size_t size = old->size * 2;
  size_t sz = sizeof(Hashtable) + size*old->bucket_size*sizeof(void*);
  Hashtable* h = malloc(sz);
  if (h == NULL) exit(1);
  memset(h, 0, sz);
  h->size = size;
  h->bucket_size = old->bucket_size;
  size_t max = old->size*old->bucket_size;
  for (size_t i = 0; i < max; ++i) {
    if (old->data[i] != NULL)
      Hashtable_add(h, old->data[i]);
  }
  *ht = h;
  free(old);
}

static uint32_t Hashtable_h(void* k) {
  uint32_t a = (uintptr_t)k >> PAGE_IDX_BITS;
  a = (a ^ 61) ^ (a >> 16);
  a = a + (a << 3);
  a = a ^ (a >> 4);
//  a = a * 0x27d4eb2d;
//  a = a ^ (a >> 15);
  return a;
}

static void Hashtable_occ(Hashtable* ht);
static Rboolean Hashtable_add(Hashtable* ht, void* p) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size-1));
  long el  = 0;
  while (ht->data[idx + el] != 0 && el < ht->bucket_size) {
    ++el;
  }
  if (el == ht->bucket_size) {
    return FALSE;
  }
  CHECK(ht->data[idx + el] == 0);
  CHECK(el >= 0 && el < ht->bucket_size);
  ht->data[idx + el] = p;
  return TRUE;
}

static __attribute__ ((always_inline)) Rboolean Hashtable_get(Hashtable* ht, void* p) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size-1));
  long el  = 0;
  while (el < ht->bucket_size) {
    if (ht->data[idx + el] == p)
      return TRUE;
    if (ht->data[idx + el] == 0)
      return FALSE;
    ++el;
  }
  return FALSE;
}

static void Hashtable_remove(Hashtable* ht, void* p) {
  long key = Hashtable_h(p);
  long idx = ht->bucket_size * (key & (ht->size-1));
  long el  = 0;
  while (el < ht->bucket_size) {
    if (ht->data[idx + el] == p) {
      while (el < ht->bucket_size) {
        ht->data[idx + el] = ht->data[idx + el + 1];
        ++el;
      }
      ht->data[idx + el - 1] = 0;
      CHECK(Hashtable_get(ht, p) == FALSE);
      return;
    }
    el++;
  }
  CHECK(0);
}

static void Hashtable_occ(Hashtable* ht) {
  size_t used = 0;
  for (size_t i = 0; i < ht->size * ht->bucket_size; ++i) {
    if (ht->data[i] != 0)
      ++used;
  }
  printf("HT usage: %f\n", (double)used / (double)(ht->size * ht->bucket_size));
}

  static size_t gc_cnt = 0;
  static Rboolean fullCollection = FALSE;

#define CONS_BUCKET 0
#define NUM_BUCKETS 17
  static size_t BUCKET_SIZE[NUM_BUCKETS] = {40, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 128, 160, 192, 256, 320, 512};
  static size_t INITIAL_PAGE_LIMIT[NUM_BUCKETS] = {1500, 400, 100, 100, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 10, 20};
  static size_t INITIAL_BIG_OBJ_LIMIT = 6 * 1024 * 1024;
  static double PAGE_FULL_TRESHOLD = 0.04;
  static double GROW_RATE = 1.2;

  static inline size_t roundUp(size_t bs, size_t cs) {
    size_t res = bs / cs;
    if (res * cs >= bs)
      return res;
    return res+1;
  }

  typedef struct CellInfo {
    unsigned char mark : 2;
    unsigned char used : 1;
  } CellInfo;

  typedef struct Page {
    CellInfo info[MAX_IDX];
    unsigned bkt  : 8;
    unsigned live : 1;
    unsigned old  : 1;
    struct Page* next;
    uintptr_t end;
    uintptr_t finger;
    uintptr_t sweep_finger;
    uintptr_t sweep_end;
    size_t free_nodes;
    size_t available_nodes;
    char data[];
  } Page;

  typedef struct BigObject {
    CellInfo info;
    struct BigObject* next;
    size_t size;
    char data[];
  } BigObject;

#define PTR2PAGE(ptr) ((Page*)((uintptr_t)(ptr) & ~PAGE_MASK))
#define PTR2IDX(ptr) (((uintptr_t)(ptr) & PAGE_MASK) >> PAGE_IDX_BITS)
#define PTR2BIG(ptr) ((BigObject*)((uintptr_t)(ptr) - sizeof(BigObject)))
#define ISBIG(ptr) ptr->sxpinfo.big
#define ISMARKED(s) (ISBIG(s) \
    ? PTR2BIG(s)->info.mark != MARK_WHITE \
    : PTR2PAGE(s)->info[PTR2IDX(s)].mark != MARK_WHITE)
#define PTR2INFO(s) (ISBIG(s) \
    ? &PTR2BIG(s)->info \
    : &PTR2PAGE(s)->info[PTR2IDX(s)])

  void verifyPage(Page* page) {
    CHECK(page->next == NULL);
    for (size_t i = PTR2IDX((SEXP)page->data); i < PTR2IDX((void*)page->end); ++i) {
      CHECK(page->info[i].used == 0);
      CHECK(page->info[i].mark == MARK_WHITE);
      CHECK((void*)&page->info[i] >= (void*)page &&
          (void*)&page->info[i] < (void*)page->finger);
      CHECK((void*)&page->data[i] >= (void*)page->finger &&
          (void*)&page->data[i] < (void*)page->end);
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
    memset(data, 0, PAGE_SIZE);
    Page* page = (Page*)data;
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
  page->free_nodes = page->available_nodes = available / BUCKET_SIZE[bkt];
  page->sweep_finger = page->sweep_end = (uintptr_t)page->data;
  // printf("allocated a %d page %p from %p to %p\n", bkt, page, page->finger, page->end);
  verifyPage(page);
  return page;
}

typedef struct SizeBucket {
  Page* cur;
  Page* pages;
  Page* next_to_sweep;
  size_t page_limit;
  size_t num_pages;
} SizeBucket;

struct {
  SizeBucket sizeBucket[NUM_BUCKETS];
  BigObject* bigObjects;
  Hashtable* bigObjectsHt;
  Hashtable* pageHt;
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
    bucket->page_limit = INITIAL_PAGE_LIMIT[i];
    bucket->num_pages = 0;
  }
  HEAP.bigObjects = NULL;
  HEAP.bigObjectSize = 0;
  HEAP.bigObjectLimit = INITIAL_BIG_OBJ_LIMIT;
  HEAP.size = 0;
  Hashtable_init(&HEAP.bigObjectsHt);
  Hashtable_init(&HEAP.pageHt);
  heapIsInitialized = 1;
}

static inline Rboolean isValidSexp(void* ptr) {
  Page* page = PTR2PAGE(ptr);
  if (page == NULL)
    return FALSE;
  if (Hashtable_get(HEAP.pageHt, page)) {
    Rboolean aligned =
      ((uintptr_t)ptr - (uintptr_t)page->data) % BUCKET_SIZE[page->bkt];
    return aligned == 0 && page->info[PTR2IDX(ptr)].used == 1;
  }
  return Hashtable_get(HEAP.bigObjectsHt, ptr);
}

static inline Rboolean isValidSexpSlow(void* ptr) {
  BigObject* o = HEAP.bigObjects;
  while (o != NULL) {
    if (((uintptr_t)ptr - sizeof(BigObject)) == (uintptr_t)o)
      return TRUE;
    o = o->next;
  }
  Page* page = PTR2PAGE(ptr);
  size_t idx = PTR2IDX(ptr);
  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    Page* cur = HEAP.sizeBucket[i].pages;
    while (cur != NULL) {
      if (cur == page) {
        Rboolean aligned =
          ((uintptr_t)ptr - (uintptr_t)cur->data) % BUCKET_SIZE[cur->bkt];
        return aligned == 0 && page->info[idx].used == 1;
      }
      cur = cur->next;
    }
  }
  return FALSE;
}


SEXP alloc(size_t sz);

static void* allocBigObj(size_t sexp_sz) {
  size_t sz = sizeof(BigObject) + sexp_sz;

  if (HEAP.bigObjectSize + sz > HEAP.bigObjectLimit)
    doGc(NUM_BUCKETS);
  // TODO need grow?

  BigObject* obj = malloc(sz);
  if (obj == NULL)
    Rf_errorcall(R_NilValue, "error alloc");

  memset(obj, 0, sz);
  // printf("Malloced big %p\n", obj);

  obj->info.used = 1;
  obj->next = HEAP.bigObjects;
  obj->size = sz;

  HEAP.bigObjects = obj;
  HEAP.bigObjectSize += sz;

  while (!Hashtable_add(HEAP.bigObjectsHt, obj->data))
    Hashtable_grow(&HEAP.bigObjectsHt);

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

  while (!Hashtable_add(HEAP.pageHt, page))
    Hashtable_grow(&HEAP.pageHt);
}

static void* findPageToSweep(SizeBucket* bucket) {
  Page* page = bucket->next_to_sweep;
  while (page != NULL) {
    CHECK(page->sweep_finger <= page->sweep_end);
    if (page->sweep_finger <= page->sweep_end) {
      double free = (double)page->free_nodes / (double)page->available_nodes;
      if (free > PAGE_FULL_TRESHOLD)
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
      if (page->info[i].mark == MARK_WHITE) {
        if (page->info[i].used == 0) {
          page->info[i].used = 1;
          page->free_nodes--;
        }
        memset(res, 0, BUCKET_SIZE[bkt]);
        page->sweep_finger = finger;
        return res;
      } else {
        if (fullCollection)
          page->info[i].mark = MARK_WHITE;
        else
          page->old = 1;
      }
    }
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
  if (bucket->page_limit <= bucket->num_pages) {
    doGc(bkt);
    // TODO: something a more sane...
    return allocInBucket(bkt);
  }

  if (bucket->page_limit <= bucket->num_pages) {
    puts("fatal, run out of space");
    exit(2);
  }

  growBucket(bkt);

  {
    Page* page = bucket->cur;
    void* res = (void*)page->finger;
    size_t i = PTR2IDX(res);
    CHECK(page->info[i].used == 0);
    page->info[i].used = 1;
    page->finger += BUCKET_SIZE[bkt];
    page->free_nodes--;
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
      CHECK(page->info[i].used == 0);
      page->info[i].used = 1;
      page->finger = next;
      page->free_nodes--;
      return res;
    }
  }
  CHECK(page == NULL || page->finger == page->end);
  return slowAllocInBucket(bkt);
}

SEXP alloc(size_t sz) {
  unsigned bkt = 1;
  while (bkt < NUM_BUCKETS && BUCKET_SIZE[bkt] < sz) ++bkt;
  if (bkt < NUM_BUCKETS) {
    SEXP res = (SEXP)allocInBucket(bkt);
    // printf("allo %p for %d in %d\n", res, sz, BUCKET_SIZE[bkt]);
    CHECK(PTR2PAGE(res)->info[PTR2IDX(res)].used == 1);
    res->sxpinfo.big = 0;
    return res;
  }
  SEXP res = (SEXP) allocBigObj(sz);
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

#define MS_SIZE 40000
static SEXP MarkStack[MS_SIZE+2];
static size_t MSpos = 0;

static void heapStatistics() {
  printf("HEAP statistics after gc %d of gen %d: size %d\n",
      gc_cnt,
      fullCollection,
      HEAP.size / 1024 / 1024);

  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    size_t free = 0;
    size_t available = 0;
    Page* p = HEAP.sizeBucket[i].pages;
    while (p != NULL) {
      free += p->free_nodes;
      available += p->available_nodes;
      p = p->next;
    }
    printf(" Bucket %d (%d) : pages %d / %d, nodes free %d   (%f)\n",
        i, BUCKET_SIZE[i],
        HEAP.sizeBucket[i].num_pages,
        HEAP.sizeBucket[i].page_limit,
        free,
        (float)free / (float)available);
  }
}


static double pressure(unsigned bkt) {
  if (bkt == NUM_BUCKETS) {
    return (double)HEAP.bigObjectSize / (double)HEAP.bigObjectLimit;
  }
  SizeBucket* b = &HEAP.sizeBucket[bkt];
  return (double)b->num_pages / (double)b->page_limit;
}

static void finish_sweep();
static void traceHeap();
static void traceStack();
static void free_unused_memory();
static void sweep_large_obj();
static void PROCESS_NODE(SEXP);

#include <time.h>

static double toMS(struct timespec* ts) {
  return (double)ts->tv_sec * 1000L + (double)ts->tv_nsec / 1000000.0;
}

size_t marked = 0;

void static doGc(unsigned bkt) {
#ifdef GCDEBUG
  struct timespec start;
  struct timespec end;
  marked = 0;
  clock_gettime(CLOCK_MONOTONIC, &start);
#endif

  finish_sweep();
  double p_before = pressure(bkt);

  PTR2PAGE(R_NilValue)->info[PTR2IDX(R_NilValue)].mark = MARK_BLACK;
  PROCESS_NODE(R_NilValue);

  traceStack();
  traceHeap();
  CHECK(MSpos == 0);

  free_unused_memory();

  gc_cnt++;
//  if (gc_cnt % 10 == 0)
//     heapStatistics();

  double p_after = pressure(bkt);
  double relief = p_before-p_after;

  if (relief < 0.2 && fullCollection) {
    if (bkt == NUM_BUCKETS) {
      HEAP.bigObjectLimit *= GROW_RATE;
    } else {
      HEAP.sizeBucket[bkt].page_limit *= GROW_RATE;
    }
  }

  Rboolean didfullCollection = fullCollection;
  fullCollection = relief < 0.001;

  sweep_large_obj();

#ifdef GCDEBUG
  clock_gettime(CLOCK_MONOTONIC, &end);
  printf("Gc %d (%d) of gen %d took %f to mark %d\n", gc_cnt, bkt, didfullCollection, toMS(&end)-toMS(&start), marked);
#endif
}

static void finish_sweep() {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];
    Page* p = bucket->pages;
    while (p != NULL) {
      CHECK(p->sweep_finger <= p->sweep_end && p->sweep_end <= p->finger);
        uintptr_t finger = p->sweep_finger;
        while (finger < p->sweep_end) {
        size_t i = PTR2IDX((void*)finger);
        CHECK(i < MAX_IDX);
        if (p->info[i].mark == MARK_WHITE) {
          if (p->info[i].used == 1) {
            p->info[i].used = 0;
            ON_DEBUG(memset((void*)finger, 0xde, BUCKET_SIZE[p->bkt]));
            p->free_nodes++;
          }
        } else {
          if (fullCollection)
            p->info[i].mark = MARK_WHITE;
          else
            p->old = 1;
        }
        finger += BUCKET_SIZE[p->bkt];
        CHECK(p->free_nodes <= p->available_nodes);
        p->sweep_finger = p->sweep_end;
      }
      p = p->next;
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

static void free_unused_memory(unsigned gen) {
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
        if (bucket->cur == p)
          bucket->cur = NULL;
        void * del = p;
        Hashtable_remove(HEAP.pageHt, del);
        *prevptr = p->next;
        p = p->next;
        ON_DEBUG(memset(del, 0xde, PAGE_SIZE));
        free(del);
      } else {
        // Set up the page for lazy sweeping
        p->live = 0;
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
    // No need to check gen due to sticky mark bits
    if (o->info.mark == MARK_WHITE) {
      HEAP.bigObjectSize -= o->size;
      void* del = o;
      size_t sz = o->size;
      Hashtable_remove(HEAP.bigObjectsHt, o->data);
      *prevptr = o->next;
      o = o->next;
      ON_DEBUG(memset(del, 0xde, sz));
      free(del);
    } else {
      prevptr = &o->next;
      o = o->next;
    }
  }
}

static void sweep_large_obj() {
  BigObject* o = HEAP.bigObjects;
  while (o != NULL) {
    if (o->info.mark != MARK_WHITE) {
      if (fullCollection)
        o->info.mark = MARK_WHITE;
      o = o->next;
    }
  }
}

static Page* lastPage = NULL;
static __attribute__ ((always_inline)) Rboolean markIfUnmarked(SEXP s) {
  if (!ISBIG(s)) {
    Page* p = PTR2PAGE(s);
    CHECK(Hashtable_get(HEAP.pageHt, p));
    size_t i = PTR2IDX(s);
    CellInfo info = p->info[i];
    CHECK(info.used == 1);
    if (info.mark == MARK_WHITE) {
#ifdef GCDEBUG
      ++marked;
#endif
      if (p->live == 0)
        p->live = 1;
      info.mark = MARK_BLACK;
      p->info[i] = info;
      return TRUE;
    }
    return FALSE;
  }

  CHECK(Hashtable_get(HEAP.bigObjectsHt, s));
  BigObject* o = PTR2BIG(s);
  if (o->info.mark == MARK_WHITE) {
    o->info.mark = MARK_BLACK;
    return TRUE;
  }
  return FALSE;
}

# define HAS_GENUINE_ATTRIB(x) \
    (ATTRIB(x) != R_NilValue && \
     (TYPEOF(x) != CHARSXP || TYPEOF(ATTRIB(x)) != CHARSXP))

static inline Rboolean NODE_IS_MARKED(SEXP s) {
  return ISMARKED(s);
}

static void PROCESS_NODES();
static void PUSH_NODE(SEXP);

static inline void FORWARD_NODE(SEXP s) {
  if (s == NULL || s == R_NilValue) return;
  if (markIfUnmarked(s)) {
    PROCESS_NODE(s);
  }
  PROCESS_NODES();
}

static inline void PROCESS_NODES() {
  while (MSpos > 0) {
    PROCESS_NODE(MarkStack[--MSpos]);
  }
}

static inline void PUSH_NODE(SEXP s) {
  if (s == NULL || s == R_NilValue) return;
  if (MSpos >= MS_SIZE) {
    puts("mstack overflow");
    exit(2);
  }
  if (markIfUnmarked(s)) {
    MarkStack[MSpos++] = s;
  }
}

static __attribute__ ((always_inline)) void PROCESS_NODE(SEXP cur) {
  SEXP attrib = ATTRIB(cur);

  switch (cur->sxpinfo.type) {
  case CHARSXP:
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
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur));
    break;
  case STRSXP:
  case EXPRSXP:
  case VECSXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur));
    {
      R_xlen_t i;
      for (i = 0; i < XLENGTH(cur); i++)
        PUSH_NODE(VECTOR_ELT(cur, i));
    }
    break;
  case ENVSXP:
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
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur));
    PUSH_NODE(TAG(cur));
    PUSH_NODE(CAR(cur));
    PUSH_NODE(CDR(cur));
    break;
  case EXTPTRSXP:
    if (attrib != R_NilValue)
      PUSH_NODE(ATTRIB(cur));
    PUSH_NODE(EXTPTR_PROT(cur));
    PUSH_NODE(EXTPTR_TAG(cur));
    break;
  default:
    CHECK(0);
  }
}

extern void doTraceStack() {
  void ** p = (void**)__builtin_frame_address(0);

  while ((uintptr_t)p != R_CStackStart) {
    // CHECK(isValidSexp(*p) == isValidSexpSlow(*p));
    if ((uintptr_t)*p % 2 == 0 && isValidSexp(*p)) {
      FORWARD_NODE(*p);
    }
    p += R_CStackDir;
  }
}


static void traceStack() {
    // Clobber all registers, this should spill them to the stack.
    // -> force all variables currently hold in registers to be spilled
    //    to the stack where our stackScan can find them.
    __asm__ __volatile__(
        #ifdef __APPLE__
        "push %%rbp \n\t call _doTraceStack \n\t pop %%rbp"
        #else
        "push %%rbp \n\t call doTraceStack \n\t pop %%rbp"
        #endif
        : : 
        : "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi",
        "%r8", "%r9", "%r10", "%r11", "%r12",
        "%r13", "%r14", "%r15");
}

static __attribute__ ((always_inline)) void CHECK_OLD_TO_NEW(SEXP x, SEXP y) {
  if (!fullCollection) {
    CellInfo* xi = PTR2INFO(x);
    if (!ISBIG(y)) {
      Page* p = PTR2PAGE(y);
      CellInfo* yi = &p->info[PTR2IDX(y)];
      if (yi->mark < xi->mark) {
        PUSH_NODE(y);
        PROCESS_NODES();
      }
    } else {
      CellInfo* yi = &PTR2BIG(y)->info;
      if (yi->mark < xi->mark) {
        PUSH_NODE(y);
        PROCESS_NODES();
      }
    }
  }
}

