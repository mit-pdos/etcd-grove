/-
A node's inodes (`node.go`) as pure entries.

A materialized node (`node`) holds its elements as a slice of `Inode`s (`n.inodes`), each a
flags word, a child page id and two byte slices (its key and value). The slices point into the
mapping (an inode read from a page, `ReadInodeFromPage`) or into the heap (`put` of a cloned
key, `dereference`): `inodesOwn ins es` says that the inodes `ins` are the entries `es`, each
key and value held at its own fraction (`NodeEntry.kq`, `vq`), so that what came from the
mapping can be handed back to it.

The sizes (`size`, `sizeLessThan`, `splitIndex`) only read the slices' lengths, which are in
the `Inode` values: their specs are about `ins` alone.
-/
module

public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.KeyOrder
public import Proof.go_etcd_io.bbolt.internal.common.Inodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

/-- An inode as a pure entry: its flags, child page id, key and value bytes, and the
fractions at which its key and value are held. -/
structure NodeEntry where
  flags : w32
  pgid : w64
  key : List w8
  value : List w8
  kq : DFrac
  vq : DFrac

/-- `put` at index `i`: replace element `i` (`ex`, the key was found there) or insert before it. -/
def putList {α : Type} (l : List α) (i : Nat) (ex : Bool) (x : α) : List α :=
  if ex then l.set i x else l.take i ++ x :: l.drop i

/-- What `append(s, zero)` and then `copy(s[i+1:], s[i:])` leave (`wp_slice_copy_within`), with
element `i` then set to `x`: `x` inserted before element `i`. -/
theorem insert_copy_list {A : Type} (ins : List A) (z x : A) (i : Nat) (hi : i ≤ ins.length) :
    ((ins ++ [z]).take (i + 1) ++
        ((subslice i (ins.length + 1) (ins ++ [z])).take (ins.length + 1 - (i + 1)) ++
          (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i)) ++
        (ins ++ [z]).drop (ins.length + 1)).set i x =
      ins.take i ++ x :: ins.drop i := by
  have hv : (ins ++ [z]).length = ins.length + 1 := by simp
  have h1 : subslice i (ins.length + 1) (ins ++ [z]) = (ins ++ [z]).drop i := by
    simp only [subslice]; rw [List.take_of_length_le (by omega)]
  have h2 : (subslice (i + 1) (ins.length + 1) (ins ++ [z])).drop (ins.length + 1 - i) = [] := by
    apply List.drop_of_length_le; simp [subslice]; omega
  have h3 : (ins ++ [z]).drop (ins.length + 1) = [] := List.drop_of_length_le (by omega)
  have h4 : ((ins ++ [z]).drop i).take (ins.length + 1 - (i + 1)) = ins.drop i := by
    rw [List.drop_append_of_le_length hi]
    exact List.take_left' (by simp)
  obtain ⟨y, hy⟩ : ∃ y, (ins ++ [z])[i]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have h5 : (ins ++ [z]).take (i + 1) = ins.take i ++ [y] := by
    rw [List.take_add_one, hy, List.take_append_of_le_length hi]; rfl
  rw [h1, h2, h3, h4, h5, List.append_nil, List.append_nil, List.append_assoc]
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left hi, Nat.sub_self, List.singleton_append,
    List.set_cons_zero]

theorem idxOf_of_first {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) (j : Nat)
    (hbefore : ∀ k < j, l[k]? ≠ some x) (hat : l[j]? = some x) : l.idxOf x = j := by
  induction l generalizing j with
  | nil => simp at hat
  | cons y l ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hat
      subst hat; simp
    | succ j =>
      have hy : y ≠ x := fun h => hbefore 0 (by omega) (by simp [h])
      simp only [List.idxOf_cons, beq_iff_eq, hy, ↓reduceIte]
      congr 1
      exact ih j (fun k hk => by have := hbefore (k + 1) (by omega); simpa using this) (by simpa using hat)

theorem not_mem_of_none {α : Type} (l : List α) (x : α) (h : ∀ k < l.length, l[k]? ≠ some x) :
    x ∉ l := by
  intro hm
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hm
  exact h k hk (by rw [List.getElem?_eq_getElem hk, hkx])

/-- The key of entry `i` (empty past the end). -/
def entryKey (es : List NodeEntry) (i : Nat) : List w8 := ((es[i]?).map NodeEntry.key).getD []

/-- The entries' keys increase strictly (a node's inodes are kept sorted). -/
def entriesSorted (es : List NodeEntry) : Prop :=
  ∀ i j, i < j → j < es.length → go.GoStringLt (entryKey es i) (entryKey es j)

/-- Entry `i`'s key is not below `key` (the predicate of a node's binary searches). -/
def entryGE (es : List NodeEntry) (key : List w8) (i : Int) : Bool :=
  decide (bytes.compareResult (entryKey es i.toNat) key ≠ W64 (-1))

theorem entryGE_mono (es : List NodeEntry) (key : List w8) (hs : entriesSorted es) :
    sort.IsMonoPred (entryGE es key) es.length := by
  intro i j ⟨hi, hij, hj⟩ hfi
  simp only [entryGE, decide_eq_true_eq, ne_eq, compareResult_eq_neg1] at hfi ⊢
  intro hlt
  exact hfi (goStringLt_trans (hs i.toNat j.toNat (by omega) (by omega)) hlt)

/-- `idx` is where `key` goes among the entries: every key before it is below `key`, the one
at it (if any) is not. -/
def isSearchIdx (es : List NodeEntry) (key : List w8) (idx : Nat) : Prop :=
  idx ≤ es.length ∧ (∀ k < idx, go.GoStringLt (entryKey es k) key) ∧
  (idx < es.length → ¬ go.GoStringLt (entryKey es idx) key)

/-- What `sort.Search` returns, over the entries, is a search index. -/
theorem isSearchIdx_of_search (es : List NodeEntry) (key : List w8) (idx : w64)
    (H0 : 0 ≤ sint.Z idx) (Hfound : sint.Z idx < (es.length : Int) → entryGE es key (sint.Z idx) = true)
    (Hoob : (∀ i, 0 ≤ i ∧ i < (es.length : Int) → entryGE es key i = false) → sint.Z idx = es.length)
    (Hgt : ∀ k, 0 ≤ k ∧ k < sint.Z idx → entryGE es key k = false) :
    isSearchIdx es key (sint.nat idx) := by
  have Hle : sint.Z idx ≤ (es.length : Int) := by
    refine Classical.byContradiction fun hcn => ?_
    have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
    omega
  refine ⟨by word, ?_, ?_⟩
  · intro k hk
    have := Hgt (k : Int) ⟨by omega, by word⟩
    simp only [entryGE, decide_eq_false_iff_not, ne_eq, Classical.not_not, compareResult_eq_neg1,
      Int.toNat_natCast] at this
    exact this
  · intro hk
    have := Hfound (by word)
    simp only [entryGE, decide_eq_true_eq, ne_eq, compareResult_eq_neg1] at this
    rw [show (sint.Z idx).toNat = sint.nat idx from rfl] at this
    exact this

theorem drop_cons_of_get {α : Type} (l : List α) (j : Nat) (x : α) (h : l[j]? = some x) :
    l.drop j = x :: l.drop (j + 1) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hj

theorem take_succ_of_get {α : Type} (l : List α) (j : Nat) (x : α) (h : l[j]? = some x) :
    l.take (j + 1) = l.take j ++ [x] := by
  rw [List.take_add_one, h]; rfl

/-- The nodes `ps` (location and value) are a path of parent pointers up to a root: each
node's parent is the next one, the last one has none. -/
def parentPath [FfiSyntax] : List (Loc × go_etcd_io.bbolt.node) → Prop
  | [] => False
  | [p] => p.2.parent' = null
  | p :: q :: rest => p.2.parent' = q.1 ∧ q.1 ≠ null ∧ parentPath (q :: rest)

section sizes
variable [ext : FfiSyntax]

/-- `sz` after adding, to `off`, `elsz` and the key and value lengths of each inode of `ins`
(the loop of `node.size`, in `uintptr` arithmetic). -/
def sizeFrom (elsz off : w64) (ins : List Inode) : w64 :=
  ins.foldl (fun o it => o + (elsz + it.key'.len + it.value'.len)) off

theorem sizeFrom_nil (elsz off : w64) : sizeFrom elsz off [] = off := rfl

theorem sizeFrom_append (elsz off : w64) (ins : List Inode) (it : Inode) :
    sizeFrom elsz off (ins ++ [it]) = sizeFrom elsz off ins + (elsz + it.key'.len + it.value'.len) := by
  simp [sizeFrom, List.foldl_append]

/-- `sizeLessThan`'s answer from the size `sz` so far: adding the inodes one at a time, the
size stays below `v` (checked after each one). -/
def sizeLessThanFrom (elsz v sz : w64) : List Inode → Bool
  | [] => true
  | it :: rest =>
    if uint.Z v ≤ uint.Z (sz + (elsz + it.key'.len + it.value'.len)) then false
    else sizeLessThanFrom elsz v (sz + (elsz + it.key'.len + it.value'.len)) rest

theorem sizeLessThanFrom_drop (elsz v sz : w64) (ins : List Inode) (j : Nat) (it : Inode)
    (h : ins[j]? = some it) :
    sizeLessThanFrom elsz v sz (ins.drop j) =
      if uint.Z v ≤ uint.Z (sz + (elsz + it.key'.len + it.value'.len)) then false
      else sizeLessThanFrom elsz v (sz + (elsz + it.key'.len + it.value'.len))
        (ins.drop (j + 1)) := by
  rw [drop_cons_of_get _ _ _ h]; rfl

theorem sizeLessThanFrom_nil (elsz v sz : w64) : sizeLessThanFrom elsz v sz [] = true := rfl

/-- The loop of `splitIndex(thr)` from inode `i` (the last index `idx`, the size `sz` so far)
over the inodes `l` left to it: the first inode from the third on (`i ≥ 2`) whose element would
take the size past `thr` is the split index, else the last one the loop reaches. -/
def splitIndexGo (thr : w64) : Nat → w64 → w64 → List Inode → w64 × w64
  | _, idx, sz, [] => (idx, sz)
  | i, _, sz, it :: rest =>
    if 2 ≤ uint.Z (W64 (i : Int)) ∧ uint.Z thr < uint.Z (sz + (W64 16 + it.key'.len + it.value'.len))
    then (W64 (i : Int), sz)
    else splitIndexGo thr (i + 1) (W64 (i : Int)) (sz + (W64 16 + it.key'.len + it.value'.len)) rest

/-- `splitIndex(thr)`: the split index and the size of the first page. The loop leaves the
last two inodes (`MinKeysPerPage`) to the second page. -/
def splitIndexOf (thr : w64) (ins : List Inode) : w64 × w64 :=
  splitIndexGo thr 0 (W64 0) (W64 16) (ins.take (ins.length - 2))

theorem splitIndexGo_drop (thr : w64) (i : Nat) (idx sz : w64) (l : List Inode) (it : Inode)
    (h : l[i]? = some it) :
    splitIndexGo thr i idx sz (l.drop i) =
      if 2 ≤ uint.Z (W64 (i : Int)) ∧ uint.Z thr < uint.Z (sz + (W64 16 + it.key'.len + it.value'.len))
      then (W64 (i : Int), sz)
      else splitIndexGo thr (i + 1) (W64 (i : Int)) (sz + (W64 16 + it.key'.len + it.value'.len))
        (l.drop (i + 1)) := by
  rw [drop_cons_of_get _ _ _ h]; rfl

theorem W16_eq_leaf (x : Nat) (h : x < 2 ^ 16) :
    (W16 (x : Int) = W16 2) ↔ x = leafPageFlag := by
  unfold leafPageFlag
  constructor
  · intro h'
    have := congrArg BitVec.toNat h'
    rw [toNat_W16 _ h] at this
    simpa using this
  · intro h'; subst h'; rfl

end sizes

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The inode `it` is the entry `e`. -/
def inodeIs (it : Inode) (e : NodeEntry) : IProp GF :=
  iprop(⌜it.flags' = e.flags ∧ it.pgid' = e.pgid⌝ ∗ it.key' ↦*{e.kq} e.key ∗
    it.value' ↦*{e.vq} e.value)

/-- The inodes `ins` are the entries `es`. -/
def inodesOwn (ins : List Inode) (es : List NodeEntry) : IProp GF :=
  iprop([∗list] it;e ∈ ins;es, inodeIs it e)

theorem inodesOwn_length (ins : List Inode) (es : List NodeEntry) :
    inodesOwn (GF := GF) ins es ⊢ ⌜ins.length = es.length⌝ := by
  unfold inodesOwn
  exact BigSepL2.bigSepL2_length

theorem inodesOwn_app (a b : List Inode) (c d : List NodeEntry) (h : a.length = c.length) :
    inodesOwn (GF := GF) (a ++ b) (c ++ d) ⊣⊢ inodesOwn a c ∗ inodesOwn b d := by
  unfold inodesOwn
  exact BigSepL2.bigSepL2_append (Or.inl h)

theorem inodesOwn_cons (x : Inode) (a : List Inode) (y : NodeEntry) (b : List NodeEntry) :
    inodesOwn (GF := GF) (x :: a) (y :: b) ⊣⊢ inodeIs x y ∗ inodesOwn a b := by
  unfold inodesOwn
  exact BigSepL2.bigSepL2_cons

theorem inodesOwn_nil : ⊢ inodesOwn (GF := GF) [] [] := by
  unfold inodesOwn
  exact BigSepL2.bigSepL2_nil.2

/-- The inodes around inode `i`. -/
theorem inodesOwn_split (ins : List Inode) (es : List NodeEntry) (i : Nat) (it : Inode)
    (e : NodeEntry) (h1 : ins[i]? = some it) (h2 : es[i]? = some e) :
    inodesOwn (GF := GF) ins es ⊣⊢
      inodesOwn (ins.take i) (es.take i) ∗ inodeIs it e ∗ inodesOwn (ins.drop (i + 1)) (es.drop (i + 1)) := by
  have hi1 := (List.getElem?_eq_some_iff.1 h1).1
  have hi2 := (List.getElem?_eq_some_iff.1 h2).1
  have e1 : ins = ins.take i ++ it :: ins.drop (i + 1) := by
    rw [← drop_cons_of_get _ _ _ h1, List.take_append_drop]
  have e2 : es = es.take i ++ e :: es.drop (i + 1) := by
    rw [← drop_cons_of_get _ _ _ h2, List.take_append_drop]
  have e3 : inodesOwn (GF := GF) ins es =
      inodesOwn (ins.take i ++ it :: ins.drop (i + 1)) (es.take i ++ e :: es.drop (i + 1)) := by
    rw [← e1, ← e2]
  refine (BIBase.BiEntails.of_eq e3).trans ?_
  refine (inodesOwn_app _ _ _ _ (by simp only [List.length_take]; omega)).trans ?_
  exact sep_congr .rfl (inodesOwn_cons _ _ _ _)

/-- Inserting an inode before inode `i`. -/
theorem inodesOwn_insert (ins : List Inode) (es : List NodeEntry) (i : Nat) (x : Inode)
    (e : NodeEntry) (hl : ins.length = es.length) (hi : i ≤ ins.length) :
    inodesOwn (GF := GF) ins es ∗ inodeIs x e ⊢
      inodesOwn (ins.take i ++ x :: ins.drop i) (es.take i ++ e :: es.drop i) := by
  have e3 : inodesOwn (GF := GF) ins es = inodesOwn (ins.take i ++ ins.drop i) (es.take i ++ es.drop i) := by
    rw [List.take_append_drop, List.take_append_drop]
  rw [e3]
  iintro ⟨H, Hx⟩
  icases (inodesOwn_app _ _ _ _ (by simp only [List.length_take]; omega)).1 $$ H with ⟨H1, H2⟩
  iapply (inodesOwn_app _ _ _ _ (by simp only [List.length_take]; omega)).2
  iframe H1
  iapply (inodesOwn_cons _ _ _ _).2
  iframe

/-- Replacing inode `i`, whose ownership comes back. -/
theorem inodesOwn_replace (ins : List Inode) (es : List NodeEntry) (i : Nat) (it : Inode)
    (e : NodeEntry) (x : Inode) (e' : NodeEntry) (h1 : ins[i]? = some it) (h2 : es[i]? = some e) :
    inodesOwn (GF := GF) ins es ∗ inodeIs x e' ⊢ inodesOwn (ins.set i x) (es.set i e') ∗ inodeIs it e := by
  have hi1 := (List.getElem?_eq_some_iff.1 h1).1
  have hi2 := (List.getElem?_eq_some_iff.1 h2).1
  rw [List.set_eq_take_append_cons_drop, List.set_eq_take_append_cons_drop]
  simp only [hi1, hi2, ↓reduceIte]
  iintro ⟨H, Hx⟩
  icases (inodesOwn_split ins es i it e h1 h2).1 $$ H with ⟨H1, Hie, H2⟩
  iframe Hie
  iapply (inodesOwn_app _ _ _ _ (by simp only [List.length_take]; omega)).2
  iframe H1
  iapply (inodesOwn_cons _ _ _ _).2
  iframe

/-- The key of inode `i`, out of the inodes' ownership. -/
theorem inodesOwn_key_acc (ins : List Inode) (es : List NodeEntry) (i : Nat) (it : Inode)
    (e : NodeEntry) (h1 : ins[i]? = some it) (h2 : es[i]? = some e) :
    inodesOwn (GF := GF) ins es ⊢
      it.key' ↦*{e.kq} e.key ∗ (it.key' ↦*{e.kq} e.key -∗ inodesOwn ins es) := by
  unfold inodesOwn
  iintro H
  icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it e => inodeIs (GF := GF) it e) h1 h2 $$ H
    with ⟨Hi, Hback⟩
  unfold inodeIs
  icases Hi with ⟨%Hp, Hk, Hv⟩
  iframe Hk
  iintro Hk
  iapply Hback
  iframe
  ipureintro; exact Hp

end own

end bbolt
end EtcdGrove
end Perennial
