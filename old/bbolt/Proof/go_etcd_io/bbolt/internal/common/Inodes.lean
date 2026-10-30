/-
The inodes of a page (`ReadInodeFromPage`): what each element of a page's bytes reads as, its
key and value slices pointing into the page (they are not copied), and when a page can be
read so (its elements, keys and values inside it, every key non-empty).
-/
module

public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section inodes
variable [ext : FfiSyntax]

/-- The inode element `i` of the page `pg` at `l` reads as: a leaf element's flags, key and
value, a branch element's child and key; the key and value are slices of the page. -/
def inodeOf (l : Loc) (pg : List w8) (i : Nat) : Inode :=
  if pageFlags pg = leafPageFlag then
    Inode.mk (W32 (leafFlags pg i)) (W64 0)
      (slice.mk (l +ₗ ((elemOff i + leafPos pg i : Nat) : Int)) (W64 (leafKsize pg i))
        (W64 (leafKsize pg i)))
      (slice.mk (l +ₗ ((elemOff i + leafPos pg i + leafKsize pg i : Nat) : Int))
        (W64 (leafVsize pg i)) (W64 (leafVsize pg i)))
  else
    Inode.mk (W32 0) (W64 (branchPgid pg i))
      (slice.mk (l +ₗ ((elemOff i + branchPos pg i : Nat) : Int)) (W64 (branchKsize pg i))
        (W64 (branchKsize pg i)))
      slice.nil

/-- The inodes of the page `pg` at `l`. -/
def inodesOf (l : Loc) (pg : List w8) : List Inode :=
  (List.range (pageCount pg)).map (inodeOf l pg)

/-- A leaf page that `ReadInodeFromPage` reads without panicking: well-formed, every key
non-empty. -/
def leafReadable (pg : List w8) : Prop :=
  leafWF pg pg.length ∧ ∀ i < pageCount pg, 0 < leafKsize pg i

/-- A branch page that `ReadInodeFromPage` reads without panicking. -/
def branchReadable (pg : List w8) : Prop :=
  elemOff (pageCount pg) ≤ pg.length ∧
  ∀ i < pageCount pg,
    elemOff i + branchPos pg i + branchKsize pg i ≤ pg.length ∧
    branchPos pg i + branchKsize pg i ≤ 2147483647 ∧ 0 < branchKsize pg i

/-- A page `ReadInodeFromPage` reads: a leaf page as one, any other as a branch page. -/
def pageReadable (pg : List w8) : Prop :=
  16 ≤ pg.length ∧
  (pageFlags pg = leafPageFlag → leafReadable pg) ∧
  (pageFlags pg ≠ leafPageFlag → branchReadable pg)

/-- Element `i` of a list half written up to `i` is still the filler. -/
theorem prefix_fill_lookup {α : Type} (L : List α) (z : α) (i n : Nat) (hi : i < n)
    (hL : L.length = n) : (L.take i ++ List.replicate (n - i) z)[i]? = some z := by
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left (by omega : i ≤ L.length), Nat.sub_self]
  rw [List.getElem?_replicate]; simp; omega

/-- Writing element `i` of a list half written up to `i` writes it up to `i + 1`. -/
theorem prefix_fill_set {α : Type} (L : List α) (z : α) (i n : Nat) (hi : i < n)
    (hL : L.length = n) :
    (L.take i ++ List.replicate (n - i) z).set i (L[i]'(by omega)) =
      L.take (i + 1) ++ List.replicate (n - (i + 1)) z := by
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left (by omega : i ≤ L.length), Nat.sub_self]
  rw [show n - i = (n - (i + 1)) + 1 by omega, List.replicate_succ, List.set_cons_zero,
    List.take_add_one, List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some, List.append_assoc, List.singleton_append]

theorem inodesOf_length (l : Loc) (pg : List w8) : (inodesOf l pg).length = pageCount pg := by
  simp [inodesOf]

theorem inodesOf_get (l : Loc) (pg : List w8) (i : Nat) (h : i < pageCount pg) :
    (inodesOf l pg)[i]'(by rw [inodesOf_length]; exact h) = inodeOf l pg i := by
  simp [inodesOf]

/-! ### Writing inodes onto a page (`WriteInodeToPage`) -/

/-- The bytes of the keys and values of the first `i` inodes. -/
def kvLen (ks vs : List (List w8)) (i : Nat) : Nat :=
  ((List.zipWith (fun k v => k.length + v.length) ks vs).take i).sum

/-- Where inode `i`'s key goes, from the page's start: after the header, the `n` elements
and the keys and values before it. -/
def dataOff (n : Nat) (ks vs : List (List w8)) (i : Nat) : Nat := 16 + 16 * n + kvLen ks vs i

/-- The keys and values, each key followed by its value. -/
def kvBytes (ks vs : List (List w8)) : List w8 := (List.zipWith (· ++ ·) ks vs).flatten

/-- Element `i` written for the inode `it` (key `k`, value `v`): a leaf element or a branch
element, its `pos` the distance from the element to its key. -/
def writtenElem (leaf : Bool) (n : Nat) (ks vs : List (List w8)) (it : Inode) (i : Nat) :
    List w8 :=
  let pos := W32 ((dataOff n ks vs i : Int) - (elemOff i : Int))
  if leaf then
    leafElemBytes (leafPageElement.mk it.flags' pos (W32 ((ks.getD i []).length : Int))
      (W32 ((vs.getD i []).length : Int)))
  else
    branchElemBytes (branchPageElement.mk pos (W32 ((ks.getD i []).length : Int)) it.pgid')

/-- The elements written for the inodes `ins`. -/
def writtenElems (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) : List w8 :=
  ((List.range ins.length).map fun i =>
    writtenElem leaf ins.length ks vs (ins.getD i (zero_val Inode)) i).flatten

end inodes

section write
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The inodes' keys and values hold `ks` and `vs` (at the fraction `q`). -/
def inodeData (ins : List Inode) (ks vs : List (List w8)) (q : DFrac) : IProp GF :=
  iprop([∗list] i ↦ it ∈ ins,
    it.key' ↦*{q} (ks.getD i []) ∗ it.value' ↦*{q} (vs.getD i []))

end write

section inodes2
variable [ext : FfiSyntax]

/-- The elements written for the first `j` inodes. -/
def writtenUpTo (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) (j : Nat) : List w8 :=
  ((List.range j).map fun i =>
    writtenElem leaf ins.length ks vs (ins.getD i (zero_val Inode)) i).flatten

/-- The keys and values of the first `j` inodes. -/
def kvUpTo (ks vs : List (List w8)) (j : Nat) : List w8 :=
  ((List.zipWith (· ++ ·) ks vs).take j).flatten

theorem leBytes_length' (n : Nat) (z : Int) : (leBytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [leBytes, ih]

theorem leafElemBytes_length (e : leafPageElement) : (leafElemBytes e).length = 16 := by
  simp only [leafElemBytes, List.length_append]
  rw [leBytes_length', leBytes_length', leBytes_length', leBytes_length']

theorem branchElemBytes_length (e : branchPageElement) : (branchElemBytes e).length = 16 := by
  simp only [branchElemBytes, List.length_append]
  rw [leBytes_length', leBytes_length', leBytes_length']

theorem writtenElem_length (leaf : Bool) (n : Nat) (ks vs : List (List w8)) (it : Inode) (i : Nat) :
    (writtenElem leaf n ks vs it i).length = 16 := by
  unfold writtenElem; split
  · exact leafElemBytes_length _
  · exact branchElemBytes_length _

theorem writtenUpTo_zero (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) :
    writtenUpTo leaf ks vs ins 0 = [] := rfl

theorem writtenUpTo_succ (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) (j : Nat) :
    writtenUpTo leaf ks vs ins (j + 1) = writtenUpTo leaf ks vs ins j ++
      writtenElem leaf ins.length ks vs (ins.getD j (zero_val Inode)) j := by
  simp [writtenUpTo, List.range_succ]

theorem writtenUpTo_length (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) (j : Nat) :
    (writtenUpTo leaf ks vs ins j).length = 16 * j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [writtenUpTo_succ, List.length_append, ih, writtenElem_length]; omega

theorem writtenElems_eq (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) :
    writtenElems leaf ks vs ins = writtenUpTo leaf ks vs ins ins.length := rfl

theorem kvUpTo_zero (ks vs : List (List w8)) : kvUpTo ks vs 0 = [] := by simp [kvUpTo]

theorem kvLen_zero (ks vs : List (List w8)) : kvLen ks vs 0 = 0 := by simp [kvLen]

theorem kvUpTo_succ (ks vs : List (List w8)) (j : Nat) (hk : j < ks.length) (hv : j < vs.length) :
    kvUpTo ks vs (j + 1) = kvUpTo ks vs j ++ (ks.getD j [] ++ vs.getD j []) := by
  unfold kvUpTo
  rw [List.take_add_one, List.getElem?_zipWith, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hv]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hv]

theorem kvLen_succ (ks vs : List (List w8)) (j : Nat) (hk : j < ks.length) (hv : j < vs.length) :
    kvLen ks vs (j + 1) = kvLen ks vs j + ((ks.getD j []).length + (vs.getD j []).length) := by
  unfold kvLen
  rw [List.take_add_one, List.getElem?_zipWith, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hv]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hv]

theorem kvUpTo_length (ks vs : List (List w8)) (j : Nat) (hk : j ≤ ks.length) (hv : j ≤ vs.length) :
    (kvUpTo ks vs j).length = kvLen ks vs j := by
  induction j with
  | zero => simp [kvUpTo, kvLen]
  | succ j ih =>
    rw [kvUpTo_succ _ _ _ (by omega) (by omega), kvLen_succ _ _ _ (by omega) (by omega),
      List.length_append, List.length_append, ih (by omega) (by omega)]

theorem kvLen_mono (ks vs : List (List w8)) (i j : Nat) (h : i ≤ j) : kvLen ks vs i ≤ kvLen ks vs j := by
  unfold kvLen
  have := List.take_append_drop i ((List.zipWith (fun k v => k.length + v.length) ks vs).take j)
  rw [List.take_take, Nat.min_eq_left h] at this
  rw [← this, List.sum_append]
  omega

theorem kvBytes_eq (ks vs : List (List w8)) (n : Nat) (hk : ks.length = n) (hv : vs.length = n) :
    kvBytes ks vs = kvUpTo ks vs n := by
  unfold kvBytes kvUpTo
  rw [List.take_of_length_le (by simp [List.length_zipWith]; omega)]

/-- Any 16 bytes are some leaf element's (`leafElemOf` of a page with them as element 0). -/
theorem leafElemBytes_any (e : List w8) (h : e.length = 16) :
    leafElemBytes (leafElemOf (List.replicate 16 0 ++ e) 0) = e := by
  rw [leafElemBytes_of _ 0 (by simp [elemOff, h])]
  simp [bytesAt, elemOff]
  exact List.take_of_length_le (by omega)

/-- Any 16 bytes are some branch element's. -/
theorem branchElemBytes_any (e : List w8) (h : e.length = 16) :
    branchElemBytes (branchElemOf (List.replicate 16 0 ++ e) 0) = e := by
  rw [branchElemBytes_of _ 0 (by simp [elemOff, h])]
  simp [bytesAt, elemOff]
  exact List.take_of_length_le (by omega)

end inodes2

end bbolt
end EtcdGrove
end Perennial
