/-
bbolt's pages as bytes (`internal/common/page.go`), the pure model the proofs of bbolt read pages
through (U0a of `notes/bbolt-proof-plan.md`).

A page is the bytes `pg` from its start: the 16-byte header (`common.Page`: `id`, `flags`,
`count`, `overflow`), then `count` 16-byte elements (`leafPageElement`: `flags`, `pos`, `ksize`,
`vsize`; `branchPageElement`: `pos`, `ksize`, `pgid`), then the keys and values they point to: an
element's key is `ksize` bytes `pos` bytes after the element, a leaf element's value the `vsize`
bytes after its key. The header and the elements are read through their byte encodings
(`Perennial/Golang/Theory/Unsafe.lean`'s `ByteEncoding`, the layouts of
`unsafememory/Layout.lean`), so that a typed points-to of a header or an element is a byte
points-to of these bytes (`bytesPointsto_view`).

Ported from `old/bbolt/.../PageModel.lean` (whose `leAt` decoding this replaces) and Perennial's
`unsafememory/Pages.lean` (`InodeM`, the layout `writeInodeToPage` writes), over bbolt's own
`internal/common` types.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.common
public import Perennial.Golang.Theory.Unsafe
public import Proof.go_etcd_io.bbolt.internal.common.Model
public import Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt.internal.common

section enc
variable [GooseExts]

/-! ## Byte encodings of the plain types of `internal/common` -/

instance InBucket.byteEncoding : ByteEncoding InBucket 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w64) (fun v => (v.root', v.sequence'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl) (fun _ => rfl)

instance Page.byteEncoding : ByteEncoding Page 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w16 × w16 × w32)
    (fun v => (v.id', v.flags', v.count', v.overflow'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance leafPageElement.byteEncoding : ByteEncoding leafPageElement 16 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × w32 × w32)
    (fun v => (v.flags', v.pos', v.ksize', v.vsize'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance branchPageElement.byteEncoding : ByteEncoding branchPageElement 16 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × Pgid)
    (fun v => (v.pos', v.ksize', v.pgid'))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl) (fun _ => rfl)

/-! ## Reading a page -/

/-- The `n` bytes at `off` (fewer past the end). -/
def bytesAt (pg : List w8) (off n : Nat) : List w8 := (pg.drop off).take n

/-- The page header (`(*Page)(unsafe.Pointer(&pg[0]))`). -/
def pageHdr (pg : List w8) : Page := decode (bytesAt pg 0 16)

def pageId (pg : List w8) : Nat := (pageHdr pg).id'.toNat
def pageFlags (pg : List w8) : Nat := (pageHdr pg).flags'.toNat
def pageCount (pg : List w8) : Nat := (pageHdr pg).count'.toNat
def pageOverflow (pg : List w8) : Nat := (pageHdr pg).overflow'.toNat

/-- The offset of element `i` from the page's start. -/
def elemOff (i : Nat) : Nat := 16 + 16 * i

/-- Element `i` of a leaf page. -/
def leafElem (pg : List w8) (i : Nat) : leafPageElement := decode (bytesAt pg (elemOff i) 16)
/-- Element `i` of a branch page. -/
def branchElem (pg : List w8) (i : Nat) : branchPageElement := decode (bytesAt pg (elemOff i) 16)

def leafFlags (pg : List w8) (i : Nat) : Nat := (leafElem pg i).flags'.toNat
def leafPos (pg : List w8) (i : Nat) : Nat := (leafElem pg i).pos'.toNat
def leafKsize (pg : List w8) (i : Nat) : Nat := (leafElem pg i).ksize'.toNat
def leafVsize (pg : List w8) (i : Nat) : Nat := (leafElem pg i).vsize'.toNat
def branchPos (pg : List w8) (i : Nat) : Nat := (branchElem pg i).pos'.toNat
def branchKsize (pg : List w8) (i : Nat) : Nat := (branchElem pg i).ksize'.toNat
def branchPgid (pg : List w8) (i : Nat) : Nat := (branchElem pg i).pgid'.toNat

def leafKey (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i)
def leafValue (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
def branchKey (pg : List w8) (i : Nat) : List w8 :=
  bytesAt pg (elemOff i + branchPos pg i) (branchKsize pg i)

/-- The key of element `i` of a leaf or a branch page. -/
def pageKey (pg : List w8) (i : Nat) : List w8 :=
  if pageFlags pg = 0x02 then leafKey pg i else branchKey pg i

/-! ## Constants (`internal/common/types.go`, `page.go`) -/

def branchPageFlag : Nat := 0x01
def leafPageFlag : Nat := 0x02
def metaPageFlag : Nat := 0x04
def freelistPageFlag : Nat := 0x10
/-- A leaf element's flag for a nested bucket (`BucketLeafFlag`). -/
def bucketLeafFlag : Nat := 0x01
/-- `MaxAllocSize` on amd64. -/
@[word_unfold] def maxAllocSize : Nat := 0x7FFFFFFF
/-- `BucketHeaderSize`: an `InBucket`. -/
@[word_unfold] def bucketHeaderSize : Nat := 16
/-- The meta's `freelist` when the freelist is not synced (`PgidNoFreelist`). -/
def pgidNoFreelist : Nat := 2 ^ 64 - 1
/-- `Magic`, `Version`. -/
def boltMagic : Nat := 0xED0CDAED
def boltVersion : Nat := 2

/-! ## Nested buckets -/

/-- The `InBucket` header at the start of a bucket element's value. -/
def inBucketOf (v : List w8) : InBucket := decode (bytesAt v 0 16)

/-- The root page of the nested bucket whose value is `v` (`0`: inline). -/
def inBucketRoot (v : List w8) : Nat := (inBucketOf v).root'.toNat

/-- An inline bucket's page: the value after its header. -/
def inlinePage (v : List w8) : List w8 := v.drop bucketHeaderSize

/-! ## Inodes (`ReadInodeFromPage`, `WriteInodeToPage`) -/

/-- An inode as a page stores it: flags, page id, key and value bytes (`unsafememory`'s
`InodeM`). -/
structure InodeM where
  flags : w32
  pgid : w64
  key : List w8
  value : List w8
  deriving DecidableEq

/-- The bytes of an inode's key and value in the data area. -/
def InodeM.kv (m : InodeM) : List w8 := m.key ++ m.value

/-- The data area of a page: each inode's key and value, in order. -/
def dataBytes (ms : List InodeM) : List w8 := ms.flatMap InodeM.kv

/-- The offset (from the page) of inode `i`'s key. -/
def dataOff (ms : List InodeM) (i : Nat) : Nat :=
  16 + 16 * ms.length + (dataBytes (ms.take i)).length

/-- The leaf elements `WriteInodeToPage` writes. -/
def leafElems (ms : List InodeM) : List leafPageElement :=
  ms.mapIdx fun i m => ⟨m.flags, W32 ((dataOff ms i - (16 + 16 * i) : Nat) : Int),
    W32 (m.key.length : Int), W32 (m.value.length : Int)⟩

/-- The branch elements `WriteInodeToPage` writes. -/
def branchElems (ms : List InodeM) : List branchPageElement :=
  ms.mapIdx fun i m => ⟨W32 ((dataOff ms i - (16 + 16 * i) : Nat) : Int),
    W32 (m.key.length : Int), m.pgid⟩

/-- The bytes of the elements of a leaf or a branch page. -/
def elemBytes (leaf : Bool) (ms : List InodeM) : List w8 :=
  if leaf then (leafElems ms).flatMap encode else (branchElems ms).flatMap encode

/-- The bytes of a page after its header: the elements, then the data area. -/
def pageBody (leaf : Bool) (ms : List InodeM) : List w8 := elemBytes leaf ms ++ dataBytes ms

/-- What `ReadInodeFromPage` reads back of `ms` written by `WriteInodeToPage`: a leaf page
stores no page ids, a branch page neither flags nor values. -/
def readBack (leaf : Bool) (ms : List InodeM) : List InodeM :=
  if leaf then ms.map fun m => { m with pgid := 0 }
  else ms.map fun m => { m with flags := 0, value := [] }

/-- A page can hold `ms`: the count fits a `uint16`, offsets a `uint32`, keys are not empty. -/
def pageFits (ms : List InodeM) : Prop :=
  ms.length < 2 ^ 16 ∧ 16 + (pageBody true ms).length < 2 ^ 32 ∧ ∀ m ∈ ms, m.key ≠ []

/-- Inode `i` of a page, as `ReadInodeFromPage` reads it. -/
def pageInode (pg : List w8) (i : Nat) : InodeM :=
  if pageFlags pg = leafPageFlag then
    ⟨(leafElem pg i).flags', 0, leafKey pg i, leafValue pg i⟩
  else ⟨0, (branchElem pg i).pgid', branchKey pg i, []⟩

/-- The inodes of a page (`ReadInodeFromPage`). -/
def pageInodes (pg : List w8) : List InodeM := (List.range (pageCount pg)).map (pageInode pg)

/-- A leaf page's contents: its elements' flags, keys and values. -/
def leafItems (pg : List w8) : List (Nat × List w8 × List w8) :=
  (List.range (pageCount pg)).map fun i => (leafFlags pg i, leafKey pg i, leafValue pg i)

/-- A branch page's contents: its elements' keys and children. -/
def branchItems (pg : List w8) : List (List w8 × Nat) :=
  (List.range (pageCount pg)).map fun i => (branchKey pg i, branchPgid pg i)

/-- The header `WriteInodeToPage`'s callers leave: page `id`, its flags, `count` the number of
inodes, and `overflow`. -/
def mkPageHdr (id : w64) (leaf : Bool) (n : Nat) (ovf : w32) : Page :=
  ⟨id, W16 ((if leaf then leafPageFlag else branchPageFlag : Nat) : Int), W16 (n : Int), ovf⟩

/-! ## The layout of `pageBody` (U1; ported from Perennial's `unsafememory/Pages.lean`) -/

omit [GooseExts] in
theorem flatMap_encode_length' {V : Type} {n : Nat} [ByteEncoding V n] (vs : List V) :
    (vs.flatMap encode).length = vs.length * n := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp [List.flatMap_cons, ih, ByteEncoding.encode_length, Nat.succ_mul]; omega

theorem leafElems_length (ms : List InodeM) : (leafElems ms).length = ms.length := by
  simp [leafElems]

theorem branchElems_length (ms : List InodeM) : (branchElems ms).length = ms.length := by
  simp [branchElems]

theorem elemBytes_length (leaf : Bool) (ms : List InodeM) :
    (elemBytes leaf ms).length = 16 * ms.length := by
  unfold elemBytes
  split
  · rw [flatMap_encode_length', leafElems_length]; omega
  · rw [flatMap_encode_length', branchElems_length]; omega

omit [GooseExts] in
theorem dataBytes_take_succ (ms : List InodeM) (i : Nat) (h : i < ms.length) :
    dataBytes (ms.take (i + 1)) = dataBytes (ms.take i) ++ ms[i].kv := by
  simp only [dataBytes, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton]

omit [GooseExts] in
theorem dataBytes_length_le (ms : List InodeM) (i : Nat) :
    (dataBytes (ms.take i)).length ≤ (dataBytes ms).length := by
  conv => rhs; rw [← List.take_append_drop i ms]
  simp only [dataBytes, List.flatMap_append, List.length_append]
  omega

omit [GooseExts] in
/-- The data of inode `i` in the data area. -/
theorem dataBytes_drop_take (ms : List InodeM) (i : Nat) (h : i < ms.length) :
    ((dataBytes ms).drop (dataBytes (ms.take i)).length).take ms[i].kv.length = ms[i].kv := by
  have e : dataBytes ms = dataBytes (ms.take i) ++ ms[i].kv ++ dataBytes (ms.drop (i + 1)) := by
    conv => lhs; rw [← List.take_append_drop (i + 1) ms]
    rw [show dataBytes (ms.take (i + 1) ++ ms.drop (i + 1)) =
      dataBytes (ms.take (i + 1)) ++ dataBytes (ms.drop (i + 1)) by
        simp only [dataBytes, List.flatMap_append],
      dataBytes_take_succ ms i h]
  rw [e, List.append_assoc, List.drop_left, List.take_left]

omit [GooseExts] in
theorem take_drop_append_left {α : Type} (A B : List α) (k n : Nat) (h : k + n ≤ A.length) :
    ((A ++ B).drop k).take n = (A.drop k).take n := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

omit [GooseExts] in
/-- Element `i` of the elements of a page. -/
theorem elems_take_drop {V : Type} [ByteEncoding V 16] (es : List V) (B : List w8) (i : Nat)
    (h : i < es.length) : ((es.flatMap encode ++ B).drop (16 * i)).take 16 = encode es[i] := by
  rw [take_drop_append_left _ _ _ _ (by rw [flatMap_encode_length']; omega), Nat.mul_comm,
    flatMap_encode_take_drop _ _ h]

/-- Element `i` of the leaf elements in a page's bytes. -/
theorem pageBody_leaf_elem (ms : List InodeM) (tail : List w8) (i : Nat) (h : i < ms.length) :
    ((pageBody true ms ++ tail).drop (16 * i)).take 16 =
      encode ((leafElems ms)[i]'(by rw [leafElems_length]; exact h)) := by
  simp only [pageBody, elemBytes, ite_true, List.append_assoc]
  exact elems_take_drop _ _ _ _

/-- Element `i` of the branch elements in a page's bytes. -/
theorem pageBody_branch_elem (ms : List InodeM) (tail : List w8) (i : Nat) (h : i < ms.length) :
    ((pageBody false ms ++ tail).drop (16 * i)).take 16 =
      encode ((branchElems ms)[i]'(by rw [branchElems_length]; exact h)) := by
  simp only [pageBody, elemBytes, Bool.false_eq_true, ite_false, List.append_assoc]
  exact elems_take_drop _ _ _ _

/-- The key and value of inode `i` in a page's bytes (from the end of the header). -/
theorem pageBody_kv (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat)
    (h : i < ms.length) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16)).take ms[i].kv.length = ms[i].kv := by
  have hd : dataOff ms i - 16 = (elemBytes leaf ms).length + (dataBytes (ms.take i)).length := by
    simp only [dataOff, elemBytes_length]; omega
  have hle : (dataBytes (ms.take i)).length + ms[i].kv.length ≤ (dataBytes ms).length := by
    have := dataBytes_length_le ms (i + 1)
    rw [dataBytes_take_succ ms i h, List.length_append] at this
    exact this
  rw [hd, pageBody, List.append_assoc, ← List.drop_drop, List.drop_left,
    take_drop_append_left _ _ _ _ hle, dataBytes_drop_take ms i h]

omit [GooseExts] in
theorem dataOff_succ (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    dataOff ms (j + 1) = dataOff ms j + ms[j].kv.length := by
  simp only [dataOff, dataBytes_take_succ ms j h, List.length_append]; omega

theorem pageBody_length (leaf : Bool) (ms : List InodeM) :
    (pageBody leaf ms).length = 16 * ms.length + (dataBytes ms).length := by
  simp [pageBody, elemBytes_length]

theorem dataOff_le (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    dataOff ms j + ms[j].kv.length ≤ 16 + (pageBody true ms).length := by
  rw [← dataOff_succ ms j h]
  have := dataBytes_length_le ms (j + 1)
  simp only [dataOff, pageBody, List.length_append, elemBytes_length]; omega

omit [GooseExts] in
theorem dataOff_ge (ms : List InodeM) (i : Nat) : 16 + 16 * ms.length ≤ dataOff ms i := by
  simp [dataOff]

/-- The key of inode `i` in a page's bytes (from the end of the header). -/
theorem pageBody_key' (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat)
    (h : i < ms.length) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16)).take ms[i].key.length = ms[i].key := by
  have e := congrArg (List.take ms[i].key.length) (pageBody_kv leaf ms tail i h)
  rw [List.take_take, Nat.min_eq_left (by simp [InodeM.kv])] at e
  rw [e]; simp [InodeM.kv]

/-- The value of inode `i` in a page's bytes (from the end of the header). -/
theorem pageBody_value' (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat)
    (h : i < ms.length) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16 + ms[i].key.length)).take
      ms[i].value.length = ms[i].value := by
  have e := congrArg (List.drop ms[i].key.length) (pageBody_kv leaf ms tail i h)
  rw [List.drop_take] at e
  rw [← List.drop_drop]
  have hl : ms[i].kv.length - ms[i].key.length = ms[i].value.length := by simp [InodeM.kv]
  rw [hl] at e
  rw [e]; simp [InodeM.kv]

omit [GooseExts] in
theorem readBack_length (leaf : Bool) (ms : List InodeM) :
    (readBack leaf ms).length = ms.length := by
  unfold readBack; split <;> simp

/-- The bytes at `off ≥ 16` of a page made of a header and `B`: `B`'s at `off - 16`. -/
theorem bytesAt_hdr (h : Page) (B : List w8) (off n : Nat) (hoff : 16 ≤ off) :
    bytesAt (encode h ++ B) off n = (B.drop (off - 16)).take n := by
  unfold bytesAt
  have : off = (encode h).length + (off - 16) := by rw [ByteEncoding.encode_length]; omega
  rw [this, ← List.drop_drop, List.drop_left]
  congr 2; omega

/-! ## Lemma statements (proved by U1) -/

/-- The header of bytes starting with an encoded header. -/
theorem pageHdr_bytes (h : Page) (rest : List w8) : pageHdr (encode h ++ rest) = h := by
  unfold pageHdr bytesAt
  rw [List.drop_zero, List.take_left' (ByteEncoding.encode_length h), ByteEncoding.decode_encode]

/-- **The round trip of `WriteInodeToPage`/`ReadInodeFromPage`**: a page laid out with the
header `mkPageHdr id leaf ms.length ovf` and `pageBody leaf ms` reads back `readBack leaf ms`.
Used by U9 (`node.write`, then a later `node.read` of the written page: `treeData` of the spilled
tree) and U1 (`ReadInodeFromPage`'s spec). -/
theorem pageInodes_writeInodes (id : w64) (leaf : Bool) (ms : List InodeM) (ovf : w32)
    (tail : List w8) (h : pageFits ms) :
    pageInodes (encode (mkPageHdr id leaf ms.length ovf) ++ pageBody leaf ms ++ tail) =
      readBack leaf ms := by
  obtain ⟨hn, hb, hk⟩ := h
  rw [List.append_assoc]
  generalize hpg : encode (mkPageHdr id leaf ms.length ovf) ++ (pageBody leaf ms ++ tail) = pg
  have hhdr : pageHdr pg = mkPageHdr id leaf ms.length ovf := by rw [← hpg, pageHdr_bytes]
  have hcount : pageCount pg = ms.length := by
    simp only [pageCount, hhdr, mkPageHdr]; word
  have hflags : (pageFlags pg = leafPageFlag) = (leaf = true) := by
    simp only [pageFlags, hhdr, mkPageHdr]
    cases leaf <;> simp [leafPageFlag, branchPageFlag]
  have hbl : (pageBody true ms).length = (pageBody leaf ms).length := by
    simp [pageBody_length]
  apply List.ext_getElem
  · simp [pageInodes, hcount, readBack_length]
  intro i h1 h2
  simp only [pageInodes, List.length_map, List.length_range, hcount] at h1
  have hdo := dataOff_le ms i h1
  have hdg := dataOff_ge ms i
  have hi16 : 16 * i < 16 * ms.length := by omega
  simp only [pageInodes, List.getElem_map, List.getElem_range, pageInode, hflags]
  have hk' : ms[i].kv.length = ms[i].key.length + ms[i].value.length := by simp [InodeM.kv]
  cases leaf
  · simp only [Bool.false_eq_true, ite_false, readBack, List.getElem_map]
    have he : branchElem pg i = (branchElems ms)[i]'(by rw [branchElems_length]; exact h1) := by
      unfold branchElem
      rw [← hpg, bytesAt_hdr _ _ _ _ (by simp [elemOff]),
        show elemOff i - 16 = 16 * i by simp [elemOff], pageBody_branch_elem ms tail i h1,
        ByteEncoding.decode_encode]
    have hp : branchPos pg i = dataOff ms i - (16 + 16 * i) := by
      simp only [branchPos, he, branchElems, List.getElem_mapIdx]; word
    have hks : branchKsize pg i = ms[i].key.length := by
      simp only [branchKsize, he, branchElems, List.getElem_mapIdx]; word
    have hkey : branchKey pg i = ms[i].key := by
      unfold branchKey
      rw [hp, hks, ← hpg, bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
        show elemOff i + (dataOff ms i - (16 + 16 * i)) - 16 = dataOff ms i - 16 by
          simp [elemOff]; omega,
        pageBody_key' false ms tail i h1]
    rw [hkey, he]
    simp [branchElems, List.getElem_mapIdx]
  · simp only [ite_true, readBack, List.getElem_map]
    have he : leafElem pg i = (leafElems ms)[i]'(by rw [leafElems_length]; exact h1) := by
      unfold leafElem
      rw [← hpg, bytesAt_hdr _ _ _ _ (by simp [elemOff]),
        show elemOff i - 16 = 16 * i by simp [elemOff], pageBody_leaf_elem ms tail i h1,
        ByteEncoding.decode_encode]
    have hp : leafPos pg i = dataOff ms i - (16 + 16 * i) := by
      simp only [leafPos, he, leafElems, List.getElem_mapIdx]; word
    have hks : leafKsize pg i = ms[i].key.length := by
      simp only [leafKsize, he, leafElems, List.getElem_mapIdx]; word
    have hvs : leafVsize pg i = ms[i].value.length := by
      simp only [leafVsize, he, leafElems, List.getElem_mapIdx]; word
    have hkey : leafKey pg i = ms[i].key := by
      unfold leafKey
      rw [hp, hks, ← hpg, bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
        show elemOff i + (dataOff ms i - (16 + 16 * i)) - 16 = dataOff ms i - 16 by
          simp [elemOff]; omega,
        pageBody_key' true ms tail i h1]
    have hval : leafValue pg i = ms[i].value := by
      unfold leafValue
      rw [hp, hks, hvs, ← hpg, bytesAt_hdr _ _ _ _ (by simp [elemOff]; omega),
        show elemOff i + (dataOff ms i - (16 + 16 * i)) + ms[i].key.length - 16 =
          dataOff ms i - 16 + ms[i].key.length by simp [elemOff]; omega,
        pageBody_value' true ms tail i h1]
    rw [hkey, hval, he]
    simp [leafElems, List.getElem_mapIdx]

end enc

end bbolt
end EtcdGrove
end Perennial
