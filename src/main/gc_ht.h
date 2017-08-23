#define HASH_BUCKET_SIZE 8
#define HASH_TABLE_INIT_SIZE (1024/HASH_BUCKET_SIZE)

struct Page;

enum PageState { FRESH, SPLIT, MARKED, SWEEPING, SWEPT, FULL };

typedef struct PageHashtableEntry {
  struct Page* page;
  uint8_t last_mark;
  uint8_t state;
} PageHashtableEntry;

typedef struct PageHashtable {
  size_t size;
  PageHashtableEntry data[];
} PageHashtable;

void PageHashtable_init(PageHashtable** ht) {
  size_t size = 64;

  // make the size 1 too big to make it safe to read one element after the
  // bounds. See PageHashtable_remove_el for an example.
  size_t sz = sizeof(PageHashtable) + size * HASH_BUCKET_SIZE * sizeof(PageHashtableEntry) + sizeof(PageHashtableEntry);
  PageHashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  *ht = h;
}

Rboolean PageHashtable_add(PageHashtable* ht, PageHashtableEntry);
void PageHashtable_grow(PageHashtable** ht) {
  PageHashtable* old = *ht;
  size_t size = old->size * 2;
  size_t sz = sizeof(PageHashtable) + size * HASH_BUCKET_SIZE * sizeof(PageHashtableEntry) + sizeof(PageHashtableEntry);
  PageHashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  size_t max = old->size * HASH_BUCKET_SIZE;
  for (size_t i = 0; i < max; ++i) {
    if (old->data[i].page != NULL)
      PageHashtable_add(h, old->data[i]);
  }
  *ht = h;
  free(old);
}

FORCE_INLINE uint32_t PageHashtable_h(void* k) {
  uint32_t a = (uintptr_t)k >> PAGE_IDX_BITS;
  a = (a ^ 61) ^ (a >> 16);
  a = a + (a << 3);
  a = a ^ (a >> 4);
  a = a * 0x27d4eb2d;
  a = a ^ (a >> 15);
  return a;
}

Rboolean PageHashtable_add(PageHashtable* ht, PageHashtableEntry e) {
  uint32_t key = PageHashtable_h(e.page);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
  uint32_t end = idx + HASH_BUCKET_SIZE;
  for (;idx < end; ++idx) {
    CHECK (ht->data[idx].page != e.page);
    if (ht->data[idx].page == NULL) {
      ht->data[idx] = e;
      return TRUE;
    }
  }
  return FALSE;
}

PageHashtableEntry* PageHashtable_get(PageHashtable* ht, struct Page* p) {
  CHECK(HASH_BUCKET_SIZE == 8);

  uint32_t key = PageHashtable_h(p);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));

       if (ht->data[idx  ].page == p) return &ht->data[idx  ];
  else if (ht->data[idx+1].page == p) return &ht->data[idx+1];
  else if (ht->data[idx+2].page == p) return &ht->data[idx+2];
  else if (ht->data[idx+3].page == p) return &ht->data[idx+3];
  else if (ht->data[idx+4].page == p) return &ht->data[idx+4];
  else if (ht->data[idx+5].page == p) return &ht->data[idx+5];
  else if (ht->data[idx+6].page == p) return &ht->data[idx+6];
  else if (ht->data[idx+7].page == p) return &ht->data[idx+7];

  CHECK(0);
  return NULL;
}

void PageHashtable_remove(PageHashtable* ht, void* p) {
  uint32_t key = PageHashtable_h(p);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
  uint32_t end = idx + HASH_BUCKET_SIZE;
  for (;idx < end; ++idx) {
    if (ht->data[idx].page == p) {
      ht->data[idx].page = NULL;
      return;
    }
  }
  CHECK(0);
}

typedef struct ObjHashtableEntry {
  SEXP entry;
  uint8_t mark;
  size_t size;
} ObjHashtableEntry;

typedef struct ObjHashtable {
  size_t size;
  ObjHashtableEntry data[];
} ObjHashtable;

void ObjHashtable_init(ObjHashtable** ht) {
  size_t size = 64;

  size_t sz = sizeof(ObjHashtable) + size * HASH_BUCKET_SIZE * sizeof(ObjHashtableEntry) + sizeof(ObjHashtableEntry);
  ObjHashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  *ht = h;
}

Rboolean ObjHashtable_add(ObjHashtable* ht, ObjHashtableEntry);
void ObjHashtable_grow(ObjHashtable** ht) {
  ObjHashtable* old = *ht;
  size_t size = old->size * 2;
  size_t sz =
      sizeof(ObjHashtable) + size * HASH_BUCKET_SIZE * sizeof(ObjHashtableEntry) + sizeof(ObjHashtableEntry);
  ObjHashtable* h = malloc(sz);
  if (h == NULL)
    exit(1);
  memset(h, 0, sz);
  h->size = size;
  size_t max = old->size * HASH_BUCKET_SIZE;
  for (size_t i = 0; i < max; ++i) {
    if (old->data[i].entry != NULL)
      ObjHashtable_add(h, old->data[i]);
  }
  *ht = h;
  free(old);
}

FORCE_INLINE uint32_t ObjHashtable_h(void* k) {
  uint32_t a = (uintptr_t)k >> 1;
  a = (a ^ 61) ^ (a >> 16);
  a = a + (a << 3);
  a = a ^ (a >> 4);
  a = a * 0x27d4eb2d;
  a = a ^ (a >> 15);
  return a;
}

FORCE_INLINE Rboolean ObjHashtable_add(ObjHashtable* ht, ObjHashtableEntry e) {
  CHECK(HASH_BUCKET_SIZE == 8);
  uint32_t key = ObjHashtable_h(e.entry);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
       if (ht->data[idx  ].entry == NULL) ht->data[idx  ] = e;
  else if (ht->data[idx+1].entry == NULL) ht->data[idx+1] = e;
  else if (ht->data[idx+2].entry == NULL) ht->data[idx+2] = e;
  else if (ht->data[idx+3].entry == NULL) ht->data[idx+3] = e;
  else if (ht->data[idx+4].entry == NULL) ht->data[idx+4] = e;
  else if (ht->data[idx+5].entry == NULL) ht->data[idx+5] = e;
  else if (ht->data[idx+6].entry == NULL) ht->data[idx+6] = e;
  else if (ht->data[idx+7].entry == NULL) ht->data[idx+7] = e;
  else return FALSE;
  return TRUE;
}

FORCE_INLINE ObjHashtableEntry* ObjHashtable_get(ObjHashtable* ht, SEXP p) {
  CHECK(HASH_BUCKET_SIZE == 8);
  uint32_t key = ObjHashtable_h(p);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
       if (ht->data[idx  ].entry == p) return &ht->data[idx  ];
  else if (ht->data[idx+1].entry == p) return &ht->data[idx+1];
  else if (ht->data[idx+2].entry == p) return &ht->data[idx+2];
  else if (ht->data[idx+3].entry == p) return &ht->data[idx+3];
  else if (ht->data[idx+4].entry == p) return &ht->data[idx+4];
  else if (ht->data[idx+5].entry == p) return &ht->data[idx+5];
  else if (ht->data[idx+6].entry == p) return &ht->data[idx+6];
  else if (ht->data[idx+7].entry == p) return &ht->data[idx+7];

  R_Suicide("ht expt 6");
  return NULL;
}


Rboolean ObjHashtable_exists(ObjHashtable* ht, SEXP p) {
  uint32_t key = ObjHashtable_h(p);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
  uint32_t end = idx + HASH_BUCKET_SIZE;
  for (;idx < end; ++idx) {
    if (ht->data[idx].entry == p)
      return TRUE;
  }
  return FALSE;
}

void ObjHashtable_remove(ObjHashtable* ht, SEXP p) {
  uint32_t key = ObjHashtable_h(p);
  uint32_t idx = HASH_BUCKET_SIZE * (key & (ht->size - 1));
  uint32_t end = idx + HASH_BUCKET_SIZE;
  for (;idx < end; ++idx) {
    if (ht->data[idx].entry == p) {
      ht->data[idx].entry = NULL;
      return;
    }
  }
  CHECK(0);
}


