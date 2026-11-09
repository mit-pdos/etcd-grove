/-
# bbolt's `internal/common`: pages, metas and bucket headers as bytes (batch 4d)

bbolt keeps its file as pages of bytes (the read-only mmap, page buffers from `make` or the page
pool, a bucket's value) and reads and writes them through `unsafe` as Go structs: a page header
(`Page`: `id`, `flags`, `count`, `overflow`, 16 bytes), then `count` 16-byte elements
(`leafPageElement`: `flags`, `pos`, `ksize`, `vsize`; `branchPageElement`: `pos`, `ksize`,
`pgid`), then their keys and values, each `pos` bytes after its element; a meta page's `Meta`
(64 bytes) after the header; a freelist page's `Pgid`s after the header; a bucket value's
`InBucket` (16 bytes) with an inline page after it. Every layout is little-endian, gc's on a
64-bit target (`unsafe.Sizeof`, folded by Goose).

## The vocabulary: bytes and their decoding

The ownership of a page is **Perennial's byte points-to** `bytesPointsto p dq bs` of its bytes
`bs` from its first byte `p` (the extent: `(1 + overflow) * pageSize` bytes for a file page, a
value's bytes for an inline page): the mmap, a page buffer and a value already come as bytes, so
no predicate of this package stands between them and the page's methods. What the package adds
is the **meaning of the bytes**, as transparent pure functions (the file format is part of what
bbolt's own specs mean), and the **laws** that let a client use it without offsets:

* decoding (`hdrOf`, `leafElemOf`, `branchElemOf`, `leafKeyOf`, `leafValueOf`, `branchKeyOf`,
  `pageItems`, `freelistIdsOf`, `metaOf`, `inBucketOf`), and its well-formedness conditions
  (`pageReadable`, `pageLaidOut`, `freelistReadable`);
* encoding, what the writers leave (`withHdr`, `writeNode`, `freelistPage`, `withMeta`,
  `encMeta`, `encInBucket`);
* the addresses the methods return (`elemLoc`, `metaLoc`; the key and value slices
  `leafKeySlice`, `leafValueSlice`, `branchKeySlice`; `pageInodesAt`, what `ReadInodeFromPage`
  builds);
* the meta's checksum (`fnv64a`, `metaSum`) and validity (`metaErr`, `metaValid`).

The specs of a page's methods take `bytesPointsto p dq bs` and answer in terms of the decoded
`bs` (`p.Count()` returns `(hdrOf bs).count'`), and an element's methods are stated relative to
its page (`e = elemLoc p i`), so a client never computes an offset. The structs bbolt also keeps
typed on the heap (`tx.meta = &common.Meta{}`, `&common.InBucket{}`, an `Inode` of a node) have
specs over Go's typed points-to, and **view laws** convert the bytes of a page or a value to those
typed points-tos and back (`meta_view`, `inBucket_view`), as Perennial's `BytesView` does for a
plain struct. The keys and values a page's elements point to are lent by **access laws**
(`pageKV_access`, one slice per element, for a page laid out as `WriteInodeToPage` leaves it),
and the `Pgid`s of a freelist page by `freelistIds_view`. **Codec laws** (`hdr_withHdr`,
`writeNode_read`, `freelistPage_read`, `meta_withMeta`, `metaValid_summed`) are the round trips the
writers and readers need, as obligations: bbolt's proofs never unfold the decoders.

No opaque predicate: every resource is Perennial's (`bytesPointsto`, typed points-tos, `↦*`), so
the package has none to seal (PRINCIPLES, "Abstractions": the fewest that serve). The laws are
obligations of the package's proof (Perennial's `ByteEncoding`/`BytesView` for its five plain
types, `structFieldRef_offset` for their layouts, `ownSlice_byte_view`); none is about Perennial's
own definitions only.

## Requirement snippets (`examples/specreq/bboltinternal/common.go`, `//go:build ignore`)

`ReqNodeRoundTrip` (a node written to a page reads back), `ReqMetaRoundTrip` (a meta written to a
page validates and reads back; a meta page's fields), `ReqInlineBucket` (a bucket value's header and
inline page), `ReqElementKeys` (a cursor's element reads), `ReqFreelistPageRoundTrip` (a freelist
page written by `freelist.Write` reads back through `FreelistPageIds`), `ReqMergePgids`.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.common
public import Spec.PkgInit.go_etcd_io.bbolt.internal.common
public import Perennial.Golang.Theory.Unsafe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-! ## Layout constants (gc, 64-bit) -/

/-- `PageHeaderSize`: a `Page`. -/
def pageHeaderSize : Nat := 16
/-- `LeafPageElementSize` = `BranchPageElementSize`. -/
def elemSize : Nat := 16
/-- A `Meta`. -/
def metaSize : Nat := 64
/-- `BucketHeaderSize`: an `InBucket`. -/
def bucketHeaderSize : Nat := 16

def branchPageFlag : w16 := W16 0x01
def leafPageFlag : w16 := W16 0x02
def metaPageFlag : w16 := W16 0x04
def freelistPageFlag : w16 := W16 0x10
/-- A leaf element's flag for a nested bucket (`BucketLeafFlag`). -/
def bucketLeafFlag : w32 := W32 0x01
/-- `Magic`, `Version`. -/
def boltMagic : w32 := W32 0xED0CDAED
def boltVersion : w32 := W32 2
/-- `PgidNoFreelist`: the meta's `freelist` when the freelist is not synced. -/
def pgidNoFreelist : w64 := W64 (-1)

/-! ## Reading bytes -/

/-- The `n` bytes at `off` (fewer past the end). -/
def bytesAt (bs : List w8) (off n : Nat) : List w8 := (bs.drop off).take n

/-! ## The page header -/

/-- The header of the page whose bytes are `bs` (`(*Page)(unsafe.Pointer(&bs[0]))`). -/
def hdrOf (bs : List w8) : Page :=
  { id' := decode (bytesAt bs 0 8), flags' := decode (bytesAt bs 8 2),
    count' := decode (bytesAt bs 10 2), overflow' := decode (bytesAt bs 12 4) }

/-- A header's 16 bytes. -/
def encHdr (h : Page) : List w8 :=
  encode h.id' ++ encode h.flags' ++ encode h.count' ++ encode h.overflow'

/-- `bs` with the header `h` stored over its first 16 bytes. -/
def withHdr (bs : List w8) (h : Page) : List w8 := replaceBytes bs 0 (encHdr h)

/-! ## Elements, keys and values -/

/-- The offset of element `i` from the page's first byte. -/
def elemOff (i : Nat) : Nat := pageHeaderSize + elemSize * i

/-- Element `i` of a leaf page. -/
def leafElemOf (bs : List w8) (i : Nat) : leafPageElement :=
  { flags' := decode (bytesAt bs (elemOff i) 4), pos' := decode (bytesAt bs (elemOff i + 4) 4),
    ksize' := decode (bytesAt bs (elemOff i + 8) 4),
    vsize' := decode (bytesAt bs (elemOff i + 12) 4) }

/-- Element `i` of a branch page. -/
def branchElemOf (bs : List w8) (i : Nat) : branchPageElement :=
  { pos' := decode (bytesAt bs (elemOff i) 4), ksize' := decode (bytesAt bs (elemOff i + 4) 4),
    pgid' := decode (bytesAt bs (elemOff i + 8) 8) }

/-- The offset of leaf element `i`'s key (`pos` bytes after the element). -/
def leafKeyOff (bs : List w8) (i : Nat) : Nat := elemOff i + (leafElemOf bs i).pos'.toNat
def leafKeyOf (bs : List w8) (i : Nat) : List w8 :=
  bytesAt bs (leafKeyOff bs i) (leafElemOf bs i).ksize'.toNat
/-- A leaf element's value: the `vsize` bytes after its key. -/
def leafValueOf (bs : List w8) (i : Nat) : List w8 :=
  bytesAt bs (leafKeyOff bs i + (leafElemOf bs i).ksize'.toNat) (leafElemOf bs i).vsize'.toNat
def branchKeyOff (bs : List w8) (i : Nat) : Nat := elemOff i + (branchElemOf bs i).pos'.toNat
def branchKeyOf (bs : List w8) (i : Nat) : List w8 :=
  bytesAt bs (branchKeyOff bs i) (branchElemOf bs i).ksize'.toNat

/-- Leaf element `i` and its key and value lie in `bs`. -/
def leafElemIn (bs : List w8) (i : Nat) : Prop :=
  elemOff (i + 1) ≤ bs.length ∧
  leafKeyOff bs i + (leafElemOf bs i).ksize'.toNat + (leafElemOf bs i).vsize'.toNat ≤ bs.length

/-- Branch element `i` and its key lie in `bs`. -/
def branchElemIn (bs : List w8) (i : Nat) : Prop :=
  elemOff (i + 1) ≤ bs.length ∧ branchKeyOff bs i + (branchElemOf bs i).ksize'.toNat ≤ bs.length

/-- A leaf page (`IsLeafPage`: its flags are exactly `LeafPageFlag`); every other page is read
as a branch page by `ReadInodeFromPage`, `WriteInodeToPage` and `PageElementSize`. -/
def isLeafHdr (h : Page) : Bool := decide (h.flags' = leafPageFlag)

def pageCount (bs : List w8) : Nat := (hdrOf bs).count'.toNat

/-! ## Inodes: a page's items -/

/-- An item of a node page, as `ReadInodeFromPage` reads it and `WriteInodeToPage` writes it: a
leaf's flags, key and value (page id `0`); a branch's key and child page id (flags `0`, value
empty). -/
structure InodeM where
  flags : w32
  pgid : Pgid
  key : List w8
  value : List w8

/-- Item `i` of the page `bs`. -/
def pageItemOf (bs : List w8) (i : Nat) : InodeM :=
  if isLeafHdr (hdrOf bs) then
    ⟨(leafElemOf bs i).flags', W64 0, leafKeyOf bs i, leafValueOf bs i⟩
  else ⟨W32 0, (branchElemOf bs i).pgid', branchKeyOf bs i, []⟩

/-- **The items of the page `bs`**, in order. -/
def pageItems (bs : List w8) : List InodeM := (List.range (pageCount bs)).map (pageItemOf bs)

/-- **`ReadInodeFromPage` can read the page `bs`**: its elements, their keys and values lie in
`bs`, and every key is non-empty (it panics on an empty key). -/
def pageReadable (bs : List w8) : Prop :=
  ∀ i < pageCount bs,
    (if isLeafHdr (hdrOf bs) then leafElemIn bs i else branchElemIn bs i) ∧
    (pageItemOf bs i).key ≠ []

/-- The offsets `[start, end)` of element `i`'s key and value. -/
def itemSpan (bs : List w8) (i : Nat) : Nat × Nat :=
  if isLeafHdr (hdrOf bs) then
    (leafKeyOff bs i, leafKeyOff bs i + (leafElemOf bs i).ksize'.toNat +
      (leafElemOf bs i).vsize'.toNat)
  else (branchKeyOff bs i, branchKeyOff bs i + (branchElemOf bs i).ksize'.toNat)

/-- **The page is laid out as `WriteInodeToPage` leaves it**: readable, and the keys and values
come after the elements, each element's after the previous one's (so no two overlap). -/
def pageLaidOut (bs : List w8) : Prop :=
  pageReadable bs ∧
  (∀ i < pageCount bs, elemOff (pageCount bs) ≤ (itemSpan bs i).1) ∧
  (∀ i, i + 1 < pageCount bs → (itemSpan bs i).2 ≤ (itemSpan bs (i + 1)).1)

/-! ## Writing a node (`WriteInodeToPage`) -/

/-- The data area: each item's key, then its value (a branch item's value too, if any). -/
def nodeData (ms : List InodeM) : List w8 := ms.flatMap fun m => m.key ++ m.value

/-- The offset from the page of item `i`'s key. -/
def dataOff (ms : List InodeM) (i : Nat) : Nat :=
  elemOff ms.length + (nodeData (ms.take i)).length

/-- The elements `WriteInodeToPage` writes (each `pos` counting from the element itself). -/
def nodeElems (leaf : Bool) (ms : List InodeM) : List w8 :=
  (ms.mapIdx fun i m =>
    let pos : w32 := W32 ((dataOff ms i - elemOff i : Nat) : Int)
    if leaf then
      encode m.flags ++ encode pos ++ encode (W32 (m.key.length : Int)) ++
        encode (W32 (m.value.length : Int))
    else encode pos ++ encode (W32 (m.key.length : Int)) ++ encode m.pgid).flatten

/-- **The bytes of a node page after its header**: the elements, then the data area. -/
def nodeBody (leaf : Bool) (ms : List InodeM) : List w8 := nodeElems leaf ms ++ nodeData ms

/-- `WriteInodeToPage(ms, p)` on the page `bs`: the body after the header (leaf if `bs`'s
header says so); the header and the bytes after the body are untouched. -/
def writeNode (bs : List w8) (ms : List InodeM) : List w8 :=
  replaceBytes bs pageHeaderSize (nodeBody (isLeafHdr (hdrOf bs)) ms)

/-- What a page written with `ms` reads back: a leaf stores no page ids, a branch neither flags
nor values. -/
def readBack (leaf : Bool) (ms : List InodeM) : List InodeM :=
  if leaf then ms.map fun m => { m with pgid := W64 0 }
  else ms.map fun m => { m with flags := W32 0, value := [] }

/-- **A page can hold `ms`**: the count fits a `uint16`, every offset and size a `uint32`, and
no key is empty. -/
def nodeFits (ms : List InodeM) : Prop :=
  ms.length < 2 ^ 16 ∧ pageHeaderSize + (nodeBody true ms).length < 2 ^ 32 ∧
  ∀ m ∈ ms, m.key ≠ []

/-! ## Freelist pages -/

/-- `FreelistPageCount`: the index of the first id (in `Pgid`s after the header) and the number
of ids; a count of `0xFFFF` or more is stored in the first `Pgid`. -/
def freelistCount (bs : List w8) : Nat × Nat :=
  if (hdrOf bs).count' = W16 0xFFFF then (1, (decode (bytesAt bs 16 8) : w64).toNat)
  else (0, (hdrOf bs).count'.toNat)

/-- The ids of the freelist page `bs`, in page order. -/
def freelistIdsOf (bs : List w8) : List Pgid :=
  (List.range (freelistCount bs).2).map fun k =>
    decode (bytesAt bs (pageHeaderSize + 8 * ((freelistCount bs).1 + k)) 8)

/-- `FreelistPageIds` can read the page: a freelist page whose ids lie in `bs`, with a count
below `2^63` (an `int`; it panics otherwise). -/
def freelistReadable (bs : List w8) : Prop :=
  (hdrOf bs).flags' = freelistPageFlag ∧ (freelistCount bs).2 < 2 ^ 63 ∧
  pageHeaderSize + 8 * ((freelistCount bs).1 + (freelistCount bs).2) ≤ bs.length

/-- **The freelist page `freelist.Write` leaves** in `bs` for the sorted ids `ids`: the
header's flags `FreelistPageFlag`, its count the number `n` of ids (`0xFFFF` from `0xFFFF` on,
the count then in the first `Pgid`), the ids after it; id, overflow and the bytes after the ids
untouched. -/
def freelistPage (bs : List w8) (ids : List Pgid) : List w8 :=
  let n := ids.length
  let h := hdrOf bs
  let c : w16 := if n < 0xFFFF then W16 (n : Int) else W16 0xFFFF
  let h' : Page := ⟨h.id', freelistPageFlag, c, h.overflow'⟩
  let body := if n = 0 then [] else if n < 0xFFFF then ids.flatMap encode
    else encode (W64 (n : Int)) ++ ids.flatMap encode
  replaceBytes (withHdr bs h') pageHeaderSize body

/-! ## Bucket headers and metas -/

def encInBucket (b : InBucket) : List w8 := encode b.root' ++ encode b.sequence'

/-- The bucket header at the start of `bs` (a bucket's value). -/
def inBucketOf (bs : List w8) : InBucket :=
  { root' := decode (bytesAt bs 0 8), sequence' := decode (bytesAt bs 8 8) }

/-- A `Meta`'s 64 bytes. -/
def encMeta (m : Meta) : List w8 :=
  encode m.magic' ++ encode m.version' ++ encode m.pageSize' ++ encode m.flags' ++
    encInBucket m.root' ++ encode m.freelist' ++ encode m.pgid' ++ encode m.txid' ++
    encode m.checksum'

/-- The `Meta` of a meta page's bytes `bs` (after the header, `Page.Meta()`). -/
def metaOf (bs : List w8) : Meta :=
  let b := bs.drop pageHeaderSize
  { magic' := decode (bytesAt b 0 4), version' := decode (bytesAt b 4 4),
    pageSize' := decode (bytesAt b 8 4), flags' := decode (bytesAt b 12 4),
    root' := inBucketOf (b.drop 16), freelist' := decode (bytesAt b 32 8),
    pgid' := decode (bytesAt b 40 8), txid' := decode (bytesAt b 48 8),
    checksum' := decode (bytesAt b 56 8) }

/-- `bs` with the meta `m` after the header. -/
def withMeta (bs : List w8) (m : Meta) : List w8 := replaceBytes bs pageHeaderSize (encMeta m)

/-- **FNV-1a, 64 bits** (`hash/fnv`'s `New64a`, `Write`, `Sum64`). -/
def fnv64a (bs : List w8) : w64 :=
  bs.foldl (fun h b => (h ^^^ BitVec.setWidth 64 b) * W64 1099511628211) (W64 14695981039346656037)

/-- `Meta.Sum64`: FNV-64a over the meta's bytes before its checksum, its first 56. -/
def metaSum (m : Meta) : w64 := fnv64a ((encMeta m).take 56)

/-- The meta with its checksum set (`Meta.Write`'s `m.checksum = m.Sum64()`). -/
def metaSummed (m : Meta) : Meta := { m with checksum' := metaSum m }

end model

section errs
variable [GooseExts] [GoGlobalContext]

/-- **`Meta.Validate`'s error**: `none` for a valid meta; else the `bbolt/errors` variable whose
value it returns: `ErrInvalid` (magic), `ErrVersionMismatch` (version), `ErrChecksum`. -/
def metaErr (m : Meta) : Option GoString :=
  if m.magic' ≠ boltMagic then some go_etcd_io.bbolt.errors.ErrInvalid
  else if m.version' ≠ boltVersion then some go_etcd_io.bbolt.errors.ErrVersionMismatch
  else if m.checksum' ≠ metaSum m then some go_etcd_io.bbolt.errors.ErrChecksum
  else none

def metaValid (m : Meta) : Prop := metaErr m = none

end errs

section locs
variable [GooseExts]

/-- A byte slice of `n` bytes at `l`, length and capacity `n` (`UnsafeByteSlice(l, 0, 0, n)`). -/
def bslice (l : Loc) (n : Nat) : GoSlice := slice.mk l (W64 (n : Int)) (W64 (n : Int))

/-- **The address of element `i`** of the page at `p` (`LeafPageElement(i)`,
`BranchPageElement(i)`, `&LeafPageElements()[i]`). -/
def elemLoc (p : Loc) (i : Nat) : Loc := p +ₗ ((elemOff i : Nat) : Int)

/-- The meta after the header of the page at `p` (`p.Meta()`). -/
def metaLoc (p : Loc) : Loc := p +ₗ (pageHeaderSize : Int)

/-- The slices `elem.Key()`/`elem.Value()` return for element `i` of the page `bs` at `p`. -/
def leafKeySlice (p : Loc) (bs : List w8) (i : Nat) : GoSlice :=
  bslice (p +ₗ (leafKeyOff bs i : Int)) (leafElemOf bs i).ksize'.toNat
def leafValueSlice (p : Loc) (bs : List w8) (i : Nat) : GoSlice :=
  bslice (p +ₗ ((leafKeyOff bs i + (leafElemOf bs i).ksize'.toNat : Nat) : Int))
    (leafElemOf bs i).vsize'.toNat
def branchKeySlice (p : Loc) (bs : List w8) (i : Nat) : GoSlice :=
  bslice (p +ₗ (branchKeyOff bs i : Int)) (branchElemOf bs i).ksize'.toNat

/-- The key slice of item `i` of the page `bs` at `p`, leaf or branch. -/
def itemKeySlice (p : Loc) (bs : List w8) (i : Nat) : GoSlice :=
  if isLeafHdr (hdrOf bs) then leafKeySlice p bs i else branchKeySlice p bs i
/-- The value slice of item `i` (a branch item: `nil`). -/
def itemValueSlice (p : Loc) (bs : List w8) (i : Nat) : GoSlice :=
  if isLeafHdr (hdrOf bs) then leafValueSlice p bs i else slice.nil

/-- **Inode `i` of the page `bs` at `p`**, as `ReadInodeFromPage` builds it: the item's flags and
page id, its key and value as slices into the page. -/
def pageInodeAt (p : Loc) (bs : List w8) (i : Nat) : Inode :=
  { flags' := (pageItemOf bs i).flags, pgid' := (pageItemOf bs i).pgid,
    key' := itemKeySlice p bs i, value' := itemValueSlice p bs i }

def pageInodesAt (p : Loc) (bs : List w8) : List Inode :=
  (List.range (pageCount bs)).map (pageInodeAt p bs)

/-- The slice of the `n` elements of the page at `p` (`LeafPageElements()`,
`BranchPageElements()`; `nil` when `n = 0`). -/
def elemsSlice (p : Loc) (n : Nat) : GoSlice :=
  if n = 0 then slice.nil else slice.mk (elemLoc p 0) (W64 (n : Int)) (W64 (n : Int))

/-- The `[]Pgid` of the freelist page `bs` at `p` (`FreelistPageIds()`; `nil` when empty). -/
def freelistIdsSlice (p : Loc) (bs : List w8) : GoSlice :=
  if (freelistCount bs).2 = 0 then slice.nil
  else slice.mk (p +ₗ ((pageHeaderSize + 8 * (freelistCount bs).1 : Nat) : Int))
    (W64 ((freelistCount bs).2 : Int)) (W64 ((freelistCount bs).2 : Int))

end locs

/-! ## Laws -/

section pure_laws
variable [GooseExts]

/-- A header stored in a page reads back; the length is kept. -/
def hdr_withHdr.spec : Prop := ∀ (bs : List w8) (h : Page),
  pageHeaderSize ≤ bs.length →
  hdrOf (withHdr bs h) = h ∧ (withHdr bs h).length = bs.length ∧
  (withHdr bs h).drop pageHeaderSize = bs.drop pageHeaderSize

/-- **A node written to a page reads back** (`WriteInodeToPage`, then `ReadInodeFromPage`): with
the header's count the number of items and the body inside the page, the header is unchanged, the
page is laid out, and its items are `ms` as the page stores them. -/
def writeNode_read.spec : Prop := ∀ (bs : List w8) (ms : List InodeM),
  nodeFits ms → (hdrOf bs).count'.toNat = ms.length →
  pageHeaderSize + (nodeBody true ms).length ≤ bs.length →
  hdrOf (writeNode bs ms) = hdrOf bs ∧ (writeNode bs ms).length = bs.length ∧
  pageLaidOut (writeNode bs ms) ∧
  pageItems (writeNode bs ms) = readBack (isLeafHdr (hdrOf bs)) ms

/-- **A freelist page reads back**: `freelist.Write`'s page, read by `FreelistPageIds`. -/
def freelistPage_read.spec : Prop := ∀ (bs : List w8) (ids : List Pgid),
  ids.length < 2 ^ 63 →
  pageHeaderSize + 8 * (ids.length + 1) ≤ bs.length →
  freelistReadable (freelistPage bs ids) ∧ freelistIdsOf (freelistPage bs ids) = ids ∧
  (hdrOf (freelistPage bs ids)).id' = (hdrOf bs).id' ∧
  (hdrOf (freelistPage bs ids)).overflow' = (hdrOf bs).overflow' ∧
  (freelistPage bs ids).length = bs.length

/-- A meta stored in a page reads back, the header unchanged. -/
def meta_withMeta.spec : Prop := ∀ (bs : List w8) (m : Meta),
  pageHeaderSize + metaSize ≤ bs.length →
  metaOf (withMeta bs m) = m ∧ hdrOf (withMeta bs m) = hdrOf bs ∧
  (withMeta bs m).length = bs.length

/-- A header store leaves the meta. -/
def meta_withHdr.spec : Prop := ∀ (bs : List w8) (h : Page),
  pageHeaderSize ≤ bs.length → metaOf (withHdr bs h) = metaOf bs

end pure_laws

section errs_laws
variable [GooseExts] [GoGlobalContext]

/-- **A summed meta is valid** when its magic and version are (the checksum covers the fields
before it only). -/
def metaValid_summed.spec : Prop := ∀ (m : Meta),
  m.magic' = boltMagic → m.version' = boltVersion → metaValid (metaSummed m)

end errs_laws

section res_laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- **The meta of a meta page, as a typed `Meta`** (`p.Meta()`): the page's bytes give the
typed points-to of its meta at `metaLoc p`, and any meta stored there gives the bytes back with
it. -/
def meta_view.spec : Prop := ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  pageHeaderSize + metaSize ≤ bs.length →
  bytesPointsto (GF := GF) p dq bs ⊢
    metaLoc p ↦{dq} metaOf bs ∗ (∀ m : Meta, metaLoc p ↦{dq} m -∗ bytesPointsto p dq (withMeta bs m))

/-- **The bucket header at the start of a value, as a typed `InBucket`**
(`(*InBucket)(unsafe.Pointer(&value[0]))`). -/
def inBucket_view.spec : Prop := ∀ (l : Loc) (dq : DFrac) (bs : List w8),
  bucketHeaderSize ≤ bs.length →
  bytesPointsto (GF := GF) l dq bs ⊢
    l ↦{dq} inBucketOf bs ∗
    (∀ b : InBucket, l ↦{dq} b -∗ bytesPointsto l dq (replaceBytes bs 0 (encInBucket b)))

/-- **The keys and values of a laid-out page**: lent as the slices its inodes hold
(`pageInodesAt`), at the page's share, until all are given back. -/
def pageKV_access.spec : Prop := ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  pageLaidOut bs →
  bytesPointsto (GF := GF) p dq bs ⊢
    ([∗list] i ∈ List.range (pageCount bs),
      itemKeySlice p bs i ↦*{dq} (pageItemOf bs i).key ∗
      itemValueSlice p bs i ↦*{dq} (pageItemOf bs i).value) ∗
    (([∗list] i ∈ List.range (pageCount bs),
      itemKeySlice p bs i ↦*{dq} (pageItemOf bs i).key ∗
      itemValueSlice p bs i ↦*{dq} (pageItemOf bs i).value) -∗ bytesPointsto p dq bs)

/-- **A freelist page's ids, as a `[]Pgid`** (`FreelistPageIds()`), lent at the page's share. -/
def freelistIds_view.spec : Prop := ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  freelistReadable bs →
  bytesPointsto (GF := GF) p dq bs ⊢
    freelistIdsSlice p bs ↦*{dq} freelistIdsOf bs ∗
    (freelistIdsSlice p bs ↦*{dq} freelistIdsOf bs -∗ bytesPointsto p dq bs)

/-- **Indexing the elements slice** (`&LeafPageElements()[i]`) is element `i`'s address. -/
def elemsSlice_index.spec : Prop := ∀ (p : Loc) (n i : Nat), i < n →
  sliceIndexRef leafPageElement (i : Int) (elemsSlice p n) = elemLoc p i ∧
  sliceIndexRef branchPageElement (i : Int) (elemsSlice p n) = elemLoc p i

/-- **`DefaultPageSize`** (`os.Getpagesize()`, read-only): the OS page size. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ⊢
    ∃ n : w64, globalAddr go_etcd_io.bbolt.internal.common.DefaultPageSize ↦□ n ∗
      ⌜4096 ≤ sint.Z n ∧ sint.Z n ≤ 65536⌝

end res_laws

end BboltCommon
end EtcdGrove
end Perennial
