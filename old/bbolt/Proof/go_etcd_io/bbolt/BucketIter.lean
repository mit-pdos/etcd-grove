/-
Iterating over a bucket (`ForEach`, `ForEachBucket`, `recursivelyInspect`): the key and value
a cursor move returned, lent out of the bucket's pages to a closure.

`kvElem V kb vb v`: `kb` is the key of an element of a leaf page of the bucket, and `vb` its
value (the value slice `v` nil and `vb` empty for a nested bucket, as the public moves return).
`kv_elem_acc`: the key and value slices of the element on top of a cursor's stack, at half the
pages' fraction, out of the bucket's pages (and back).
-/
module

public import Proof.go_etcd_io.bbolt.BucketRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- `kb` and `vb` are the key and value of an element of a leaf page of the bucket (`vb` empty
and the value slice `v` nil for a nested bucket). -/
def kvElem (V : BktView) (kb vb : List w8) (v : GoSlice) : Prop :=
  ∃ pid p pg i, V.pageAt pid = some (p, pg) ∧ pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
    kb = leafKey pg i ∧
    ((W32 (leafFlags pg i) &&& W32 1 = W32 0 ∧ vb = leafValue pg i) ∨
     (W32 (leafFlags pg i) &&& W32 1 ≠ W32 0 ∧ v = slice.nil ∧ vb = []))

/-- `kb` is the key of an element of a leaf page of the bucket, with the flags `f`. -/
def kvAt (V : BktView) (kb : List w8) (f : w32) : Prop :=
  ∃ pid p pg i, V.pageAt pid = some (p, pg) ∧ pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
    kb = leafKey pg i ∧ f = W32 (leafFlags pg i)

/-- `kb` is the name of a nested bucket of the bucket (a leaf element with `BucketLeafFlag`). -/
def bktElem (V : BktView) (kb : List w8) : Prop :=
  ∃ f, kvAt V kb f ∧ f &&& W32 1 ≠ W32 0

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem bytes_split' (l : Loc) (bs : List w8) (a b c : Qp) (h : c = a + b) :
    bytesPointsto (GF := GF) l (DFrac.own c) bs ⊣⊢
      bytesPointsto l (DFrac.own a) bs ∗ bytesPointsto l (DFrac.own b) bs := by
  rw [h]; exact bytes_split l bs a b

/-- A move that returned a non-nil key: the element on top of the stack, inside its leaf. -/
theorem kvOK_some (V : BktView) (es : List elemRef) (k v : GoSlice) (f : w32) (hok : V.ok)
    (h : kvOK V es k v f) (hk : k ≠ slice.nil) :
    ∃ r pg, leafTop V es r pg ∧ (k, v, f) = kvResult r.page' pg (sint.Z r.index') ∧
      0 ≤ sint.Z r.index' ∧ sint.Z r.index' < pageCount pg := by
  rcases h with ⟨hk0, -, -⟩ | ⟨r, pg, hlt, he⟩
  · exact absurd hk0 hk
  · refine ⟨r, pg, hlt, he, ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hli, -⟩ := leafTop_facts V es r pg hok hlt
    by_cases hc : pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z r.index'
    · unfold kvResult at he; rw [if_pos hc] at he; cases he; exact absurd rfl hk
    · have hc1 : pageCount pg ≠ 0 := fun h => hc (Or.inl h)
      have hc2 : sint.Z r.index' < pageCount pg := by
        have := fun h => hc (Or.inr h); omega
      exact ⟨hli.2.elim id (fun h => absurd h.2 hc1), hc2⟩

/-- The key and value of the element on top of a cursor's stack, at half the pages' fraction,
out of the bucket's pages (and back). -/
theorem kv_elem_acc (V : BktView) (q : Qp) (es : List elemRef) (r : elemRef) (pg : List w8)
    (hok : V.ok) (hlt : leafTop V es r pg) (h0 : 0 ≤ sint.Z r.index')
    (hin : sint.Z r.index' < pageCount pg) :
    bktPages (GF := GF) V q ⊢ ∃ kb vb,
      ⌜kvElem V kb vb (kvVal (kvResult r.page' pg (sint.Z r.index')).2.1
        (kvResult r.page' pg (sint.Z r.index')).2.2) ∧
        kvAt V kb (kvResult r.page' pg (sint.Z r.index')).2.2⌝ ∗
      (kvResult r.page' pg (sint.Z r.index')).1 ↦*{DFrac.own q.half} kb ∗
      kvVal (kvResult r.page' pg (sint.Z r.index')).2.1
        (kvResult r.page' pg (sint.Z r.index')).2.2 ↦*{DFrac.own q.half} vb ∗
      ((kvResult r.page' pg (sint.Z r.index')).1 ↦*{DFrac.own q.half} kb -∗
       kvVal (kvResult r.page' pg (sint.Z r.index')).2.1
        (kvResult r.page' pg (sint.Z r.index')).2.2 ↦*{DFrac.own q.half} vb -∗ bktPages V q) := by
  obtain ⟨pid, pre, -, -, -, hpa, -, -, hfl, hlw, -, hcar⟩ := leafTop_facts V es r pg hok hlt
  obtain ⟨i, hi⟩ : ∃ i : Nat, (i : Int) = sint.Z r.index' := ⟨_, Int.toNat_of_nonneg h0⟩
  have hit : (sint.Z r.index').toNat = i := by omega
  have hic : i < pageCount pg := by omega
  rw [kv_inside r.page' pg _ h0 hin]
  simp only [hit]
  iintro Hpgs
  icases bktPages_acc V q pid _ pg hok hpa $$ Hpgs with ⟨Hpg, Hback⟩
  icases (bytes_split' r.page' pg q.half q.half q (Qp.half_add_half q).symm).1 $$ Hpg with ⟨Hp1, Hp2⟩
  icases leaf_key_acc r.page' _ pg i hlw hic hcar $$ Hp1 with ⟨Hk, Hkback⟩
  by_cases hf : W32 (leafFlags pg i) &&& W32 1 = W32 0
  · have hv : kvVal (sliceAt r.page' (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i))
        (W32 (leafFlags pg i)) =
        sliceAt r.page' (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i) := by
      unfold kvVal; rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
    rw [hv]
    icases leaf_value_acc r.page' _ pg i hlw hic hcar $$ Hp2 with ⟨Hv, Hvback⟩
    iexists leafKey pg i, leafValue pg i
    iframe Hk Hv
    isplitr
    · ipureintro
      exact ⟨⟨pid, _, pg, i, hpa, hfl, hic, rfl, Or.inl ⟨hf, rfl⟩⟩, ⟨pid, _, pg, i, hpa, hfl, hic, rfl, rfl⟩⟩
    iintro Hk Hv
    ihave Hp1 := Hkback $$ Hk
    ihave Hp2 := Hvback $$ Hv
    iapply Hback
    iapply (bytes_split' r.page' pg q.half q.half q (Qp.half_add_half q).symm).2
    iframe
  · have hv : kvVal (sliceAt r.page' (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i))
        (W32 (leafFlags pg i)) = slice.nil := by
      unfold kvVal; rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]
    rw [hv]
    iexists leafKey pg i, []
    iframe Hk
    isplitr
    · ipureintro
      exact ⟨⟨pid, _, pg, i, hpa, hfl, hic, rfl, Or.inr ⟨hf, rfl, rfl⟩⟩, ⟨pid, _, pg, i, hpa, hfl, hic, rfl, rfl⟩⟩
    isplitl []
    · iapply ownSlice_nil
    iintro Hk -
    ihave Hp1 := Hkback $$ Hk
    iapply Hback
    iapply (bytes_split' r.page' pg q.half q.half q (Qp.half_add_half q).symm).2
    iframe

end lemmas

end bbolt
end EtcdGrove
end Perennial
