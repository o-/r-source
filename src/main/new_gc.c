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


#define BIG_OBJ_ALIGN  64
#define PAGE_SIZE      0x4000
#define PAGE_IDX       32
#define PAGE_IDX_BITS  5
#define PAGE_MASK      0x3fff
#define MAX_IDX (PAGE_SIZE/PAGE_IDX)
#define MARK_BLACK 2
#define MARK_GREY  1
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
  a = a * 0x27d4eb2d;
  a = a ^ (a >> 15);
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

static inline Rboolean Hashtable_get(Hashtable* ht, void* p) {
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

#define NUM_BUCKETS 13
static size_t BUCKET_SIZE[NUM_BUCKETS] = {32, 36, 40, 48, 56, 64, 80, 96, 128, 160, 192, 256, 320};

static size_t NormalHeapLimit = 4 * 1024 * 1024;
static size_t TotalHeapLimit = 10 * 1024 * 1024;

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

typedef struct SizeInfo {
  size_t used;
  size_t free;
  size_t size;
} SizeInfo;

typedef struct Page {
  CellInfo info[MAX_IDX];
  int bkt  : 8;
  int live : 1;
  int busy : 1;
  struct Page* next;
  uintptr_t end;
  uintptr_t finger;
  uintptr_t sweep_finger;
  uintptr_t sweep_end;
  size_t free;
  char data[];
} Page;

typedef struct BigObject {
  CellInfo info;
  struct BigObject* next;
  size_t size;
  char data[];
} BigObject;

static inline Page* ptr2page(void* ptr) {
  return (Page*)((uintptr_t)ptr & ~PAGE_MASK);
}

static inline size_t ptr2idx(void* ptr) {
  return ((uintptr_t)ptr & PAGE_MASK) >> PAGE_IDX_BITS;
}

static inline BigObject* ptr2bigObj(SEXP ptr) {
  return (BigObject*)((uintptr_t)ptr - sizeof(BigObject));
}

static inline Rboolean isMarked(SEXP s) {
  if (s->sxpinfo.gccls == 0) {
    return ptr2page(s)->info[ptr2idx(s)].mark != MARK_WHITE;
  }
  CHECK(s->sxpinfo.gccls == 1);
  return ptr2bigObj(s)->info.mark != MARK_WHITE;
}

void verifyPage(Page* page) {
  CHECK(page->next == NULL);
  for (size_t i = ptr2idx((SEXP)page->data); i < ptr2idx((void*)page->end); ++i) {
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
    size_t idx = ptr2idx((void*)pos);
    CHECK(idx != last_idx);
    last_idx = idx;
    CHECK(idx >= 0 && idx <= MAX_IDX);
    CHECK(pos < (uintptr_t)page + PAGE_SIZE);
    CHECK(ptr2page((void*)pos) == page);
    pos += BUCKET_SIZE[page->bkt];
  }
  CHECK(page->end <= (uintptr_t)page + PAGE_SIZE);
}

static void doGc();

Page* allocPage(size_t bkt) {
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
  page->busy = 0;
  page->free = available / BUCKET_SIZE[bkt];
  page->sweep_finger = page->sweep_end = (uintptr_t)page->data;
  // printf("allocated a %d page %p from %p to %p\n", bkt, page, page->finger, page->end);
  verifyPage(page);
  return page;
}

typedef struct SizeBucket {
  Page* cur;
  Page* pages;
  Page* next_to_sweep;
} SizeBucket;

struct {
  SizeBucket sizeBucket[NUM_BUCKETS];
  BigObject* bigObjects;
  Hashtable* bigObjectsHt;
  Hashtable* pageHt;
  SizeInfo size;
  size_t bigObjectSize;
} HEAP;

static int heapIsInitialized = 0;
static void new_gc_initHeap() {
  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    SizeBucket* bucket = &HEAP.sizeBucket[i];
    bucket->pages = NULL;
    bucket->cur = NULL;
    bucket->next_to_sweep = NULL;
  }
  HEAP.bigObjects = NULL;
  HEAP.bigObjectSize = 0;
  HEAP.size.used = 0;
  HEAP.size.free = 0;
  HEAP.size.size = 0;
  heapIsInitialized = 1;
  Hashtable_init(&HEAP.bigObjectsHt);
  Hashtable_init(&HEAP.pageHt);
}

static inline Rboolean isValidSexp(void* ptr) {
  Page* page = ptr2page(ptr);
  if (page == NULL)
    return FALSE;
  if (Hashtable_get(HEAP.pageHt, page)) {
    Rboolean aligned =
      ((uintptr_t)ptr - (uintptr_t)page->data) % BUCKET_SIZE[page->bkt];
    Rboolean res = aligned == 0 && page->info[ptr2idx(ptr)].used == 1;
    if (res)
      CHECK(((SEXP)ptr)->sxpinfo.gccls == 0);
    return res;
  }
  if (Hashtable_get(HEAP.bigObjectsHt, ptr)) {
    CHECK(((SEXP)ptr)->sxpinfo.gccls == 1);
    return TRUE;
  }
  return FALSE;
}

static inline Rboolean isValidSexpSlow(void* ptr) {
  BigObject* o = HEAP.bigObjects;
  while (o != NULL) {
    if (((uintptr_t)ptr - sizeof(BigObject)) == (uintptr_t)o)
      return TRUE;
    o = o->next;
  }
  Page* page = ptr2page(ptr);
  size_t idx = ptr2idx(ptr);
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

  if (HEAP.bigObjectSize + sz > HEAP.size.size + TotalHeapLimit)
    doGc();

  void* data;
  int res = posix_memalign(&data, BIG_OBJ_ALIGN, sz);
  if (res != 0)
    Rf_errorcall(R_NilValue, "error alloc");

  BigObject* obj = (BigObject*)data;
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

static void growBucket(size_t bkt) {
  if (HEAP.size.size + PAGE_SIZE > NormalHeapLimit)
    doGc();

  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  Page* page = allocPage(bkt);

  page->next = bucket->pages;
  bucket->pages = page;
  bucket->cur = page;

  size_t available = page->end - page->finger;

  HEAP.size.free += available;
  HEAP.size.size += available;

  while (!Hashtable_add(HEAP.pageHt, page))
    Hashtable_grow(&HEAP.pageHt);
}

static inline void updateFreeOnAlloc(SizeBucket* bucket, size_t bucketSz, size_t sz) {
  HEAP.size.free -= bucketSz;
  HEAP.size.used += bucketSz;
}

static void* findPageToSweep(SizeBucket* bucket) {
  Page* page = bucket->next_to_sweep;
  while (page != NULL && (page->sweep_finger == page->sweep_end || page->busy)) {
    CHECK(page->sweep_finger <= page->sweep_end);
    page = page->next;
  }
  bucket->next_to_sweep = page == NULL ? NULL : page->next;
  bucket->cur = page;
}

static void* slowAllocInBucket(size_t bkt, size_t sz) {
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];

  // Lazy sweeping
  while (bucket->next_to_sweep != NULL && bucket->cur != NULL) {
    Page* page = bucket->cur;
    uintptr_t finger = page->sweep_finger;
    while (finger < page->sweep_end) {
      void* res = (void*)finger;
      size_t i = ptr2idx(res);
      CHECK(i < MAX_IDX);
      finger += BUCKET_SIZE[bkt];
      if (page->info[i].mark == MARK_WHITE) {
        if (page->info[i].used == 0) {
          page->info[i].used = 1;
          page->free--;
        }
        memset(res, 0, BUCKET_SIZE[bkt]);
        page->sweep_finger = finger;
        return res;
      } else {
        page->info[i].mark = MARK_WHITE;
      }
    }
    page->sweep_finger = page->sweep_end;
    findPageToSweep(bucket);
  }

  growBucket(bkt);
  Page* page = bucket->cur;
  void* res = (void*)page->finger;
  size_t i = ptr2idx(res);
  CHECK(page->info[i].used == 0);
  page->info[i].used = 1;
  page->finger += BUCKET_SIZE[bkt];
  updateFreeOnAlloc(bucket, BUCKET_SIZE[bkt], sz);
  return res;
}


static inline void* allocInBucket(size_t bkt, size_t sz) {
  CHECK(BUCKET_SIZE[bkt] >= sz);
  SizeBucket* bucket = &HEAP.sizeBucket[bkt];
  Page* page = bucket->cur;
  if (page != NULL) {
    size_t next = page->finger + BUCKET_SIZE[bkt];
    if (next <= page->end) {
      void* res = (void*)page->finger;
      size_t i = ptr2idx(res);
      CHECK((uintptr_t)res + BUCKET_SIZE[bkt] <= page->end);
      CHECK(ptr2page(res) == page);
      CHECK(i > 0 && i < MAX_IDX);
      CHECK(page->info[i].used == 0);
      page->info[i].used = 1;
      page->finger = next;
      page->free--;
      updateFreeOnAlloc(bucket, BUCKET_SIZE[bkt], sz);
      return res;
    }
  }
  return slowAllocInBucket(bkt, sz);
}

SEXP alloc(size_t sz) {
  size_t bkt = 0;
  while (bkt < NUM_BUCKETS && BUCKET_SIZE[bkt] < sz) ++bkt;
  if (bkt < NUM_BUCKETS) {
    SEXP res = (SEXP)allocInBucket(bkt, sz);
    res->sxpinfo.gccls = 0;
    // printf("allo %p for %d in %d\n", res, sz, BUCKET_SIZE[bkt]);
    return res;
  }
  SEXP res = (SEXP) allocBigObj(sz);
  res->sxpinfo.gccls = 1;
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

static void traceHeap();
static void finish_sweep();
static void lazy_sweep();
static void traceStack();

#define MS_SIZE 40000
static SEXP MarkStack[MS_SIZE+2];
static size_t MSpos = 0;

static size_t gc_cnt = 0;
static void heapStatistics() {
  printf("HEAP statistics after gc %d : total limit %d, small limit %d, actual size %d+%d=%d, used %d+%d=%d\n",
      gc_cnt,
      TotalHeapLimit / 1024,
      NormalHeapLimit / 1024,
      HEAP.size.size / 1024,
      HEAP.bigObjectSize / 1024,
      HEAP.size.size+HEAP.bigObjectSize / 1024,
      HEAP.size.used / 1024,
      HEAP.bigObjectSize / 1024,
      HEAP.size.used+HEAP.bigObjectSize / 1024);
  for (size_t i = 0; i < NUM_BUCKETS; ++i) {
    size_t used = 0;
    size_t wasted = 0;
    Page* p = HEAP.sizeBucket[i].pages;
    while (p != NULL) {
      used += p->end - (uintptr_t)p->data;
      wasted += p->free * BUCKET_SIZE[i];
      p = p->next;
    }
    printf(" Bucket %d (%d) : size %d, wasted %d   (%f)\n", i, BUCKET_SIZE[i],
        used  / 1024,
        wasted / 1024,
        (float)wasted / (float)(used+wasted));
  }
}

static void PROCESS_NODE(SEXP);
void static doGc() {
  // printf(".\n");
  CHECK(HEAP.size.size = HEAP.size.used + HEAP.size.free);

  finish_sweep();

  ptr2page(R_NilValue)->info[ptr2idx(R_NilValue)].mark = MARK_BLACK;
  PROCESS_NODE(R_NilValue);

  traceStack();
  traceHeap();
  CHECK(MSpos == 0);
  lazy_sweep();

  if ((double)HEAP.size.size / (double)NormalHeapLimit > 0.8) {
    NormalHeapLimit = (double)NormalHeapLimit * 1.1;
    // printf("Grow Heap to %d kb\n", NormalHeapLimit / 1024);
  }
  if (NormalHeapLimit > TotalHeapLimit)
    TotalHeapLimit = (double)NormalHeapLimit * 1.1;
  if ((double)(HEAP.bigObjectSize + HEAP.size.size) / (double)TotalHeapLimit > 0.8) {
    TotalHeapLimit = (double)TotalHeapLimit * 1.1;
    // printf("Grow Total Heap to %d kb\n", TotalHeapLimit / 1024);
  }

  ++gc_cnt;
  // if (gc_cnt % 10 == 0)
  //   heapStatistics();
}

static void finish_sweep() {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];
    Page* p = bucket->pages;
    while (p != NULL) {
      CHECK(p->sweep_finger <= p->sweep_end && p->sweep_end <= p->finger);
      uintptr_t finger = p->sweep_finger;
      while (finger < p->sweep_end) {
        size_t i = ptr2idx((void*)finger);
        CHECK(i < MAX_IDX);
        if (p->info[i].mark == MARK_WHITE) {
          if (p->info[i].used == 1) {
            p->info[i].used = 0;
            ON_DEBUG(memset((void*)finger, 0xde, BUCKET_SIZE[p->bkt]));
            p->free++;
          }
        } else {
          p->info[i].mark = MARK_WHITE;
        }
        finger += BUCKET_SIZE[p->bkt];
      }
      p->sweep_finger = p->sweep_end;
      size_t nodes = (p->end - p->finger) / BUCKET_SIZE[p->bkt];
      if ((double)p->free / (double)nodes < 0.1)
        p->busy = 1;
      else
        p->busy = 0;
      p = p->next;
    }
  }
}

static void lazy_sweep() {
  for (size_t s = 0; s < NUM_BUCKETS; ++s) {
    SizeBucket* bucket = &HEAP.sizeBucket[s];
    Page* p = bucket->pages;
    Page** prevptr = &bucket->pages;

    while (p != NULL) {
      if (p->live == 0) {
        HEAP.size.free -= p->end - p->finger;
        HEAP.size.used -= p->finger - (uintptr_t)p->data;
        HEAP.size.size -= p->end - (uintptr_t)p->data;
        if (bucket->cur == p)
          bucket->cur = NULL;
        void * del = p;
        Hashtable_remove(HEAP.pageHt, del);
        *prevptr = p->next;
        p = p->next;
        ON_DEBUG(memset(del, 0xde, PAGE_SIZE));
        free(del);
      } else {
        p->live = 0;
        p->sweep_finger = (uintptr_t)p->data;
        p->sweep_end = p->finger;
        prevptr = &p->next;
        p = p->next;
      }
    }

    bucket->next_to_sweep = bucket->pages;
  }
  BigObject* o = HEAP.bigObjects;
  BigObject** prevptr = &HEAP.bigObjects;
  while (o != NULL) {
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
      o->info.mark = MARK_WHITE;
      prevptr = &o->next;
      o = o->next;
    }
  }
}

static Page* lastPage = NULL;
static inline Rboolean markIfUnmarked(SEXP s) {
  BigObject* o = ptr2bigObj(s);
  if ((uintptr_t)o % BIG_OBJ_ALIGN != 0 || s->sxpinfo.gccls == 0) {
    CHECK (s->sxpinfo.gccls == 0);
    Page* p = ptr2page(s);
    size_t i = ptr2idx(s);
    CHECK(p->info[i].used == 1);
    if (p->info[i].mark == MARK_WHITE) {
      if (p->live == 0)
        p->live = 1;
      p->info[i].mark = MARK_BLACK;
      return TRUE;
    }
    return FALSE;
  }

  CHECK (s->sxpinfo.gccls == 1);
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
  return isMarked(s);
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

static inline void PROCESS_NODE(SEXP cur) {
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

