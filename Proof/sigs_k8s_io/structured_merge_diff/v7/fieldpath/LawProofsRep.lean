/-
**`fieldpath`'s representation laws, proved** (`fieldpath/Vocab.lean`, "Representation"), and the
representation facts the package's proofs share (injectivity of its struct values, the sealed
predicates' basic rules).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Perennial.Proof.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpL

/-- Two values with a field's deterministic projection have equal projections. -/
theorem proj_eq [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

section inj
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

include sem package_sem in
theorem versionedSet_inj : Function.Injective (intoVal (V := fieldpath.versionedSet)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have i := package_sem.versionedSet_instance
  have e1 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_set x) (i.get_set y) h))
  have e2 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_apiVersion x) (i.get_apiVersion y) h))
  have e3 := go.intoVal_inj (Expr.Val.inj (proj_eq (i.get_applied x) (i.get_applied y) h))
  cases x; cases y; simp_all

end inj

end fpL

/-! ## Laws of other packages this file rests on, until they are proved there

`value`'s `UVal.compare_*` and `isValF_canon`, `isFieldList_agree` (agent B's), the root's
`isValF_agree` (agent A's): each is used only through these names, to be replaced by the owners'
`<X>_law_holds` once they exist. -/

namespace fpL
theorem uZ : UVal.compare_eq_zero.law := sorry
theorem uA : UVal.compare_antisymm.law := sorry
theorem uT : UVal.compare_trans.law := sorry
section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
theorem valCanon : isValF_canon.law (GF := GF) := sorry
theorem flAgree : isFieldList_agree.law (GF := GF) := sorry
theorem valAgree : isValF_agree.law (GF := GF) := sorry
end
end fpL

theorem PE_compare_eq_zero_law_holds : PE.compare_eq_zero.law :=
  PE_compare_eq_zero_law_of fpL.uZ fpL.uA
theorem PE_compare_antisymm_law_holds : PE.compare_antisymm.law :=
  PE_compare_antisymm_law_of fpL.uZ fpL.uA
theorem PE_compare_trans_law_holds : PE.compare_trans.law :=
  PE_compare_trans_law_of fpL.uZ fpL.uT
theorem PE_sorted_ext_law_holds : PE.sorted_ext.law :=
  PE_sorted_ext_law_of fpL.uZ fpL.uA fpL.uT

namespace fpL

/-- `strings.Compare`'s result is `gsCompare`. -/
theorem compareResult_gs : ∀ a b : GoString, (strings.compareResult a b).toInt = gsCompare a b
  | [], [] => by decide
  | [], _ :: _ => by
    simp only [strings.compareResult, gsCompare]
    rw [if_pos (show go.GoStringLt [] _ from List.Lex.nil)]; decide
  | _ :: _, [] => by
    simp only [strings.compareResult, gsCompare]
    rw [if_neg (by intro h; cases h), if_neg (by simp)]; decide
  | x :: xs, y :: ys => by
    have ih := compareResult_gs xs ys
    simp only [strings.compareResult, gsCompare] at ih ⊢
    have hlt : go.GoStringLt (x :: xs) (y :: ys) ↔
        uint.Z x < uint.Z y ∨ (x = y ∧ go.GoStringLt xs ys) := by
      unfold go.GoStringLt
      constructor
      · intro h; cases h with
        | rel h => exact Or.inl h
        | cons h => exact Or.inr ⟨rfl, h⟩
      · rintro (h | ⟨rfl, h⟩)
        · exact List.Lex.rel h
        · exact List.Lex.cons h
    have hz : ∀ a b : w8, uint.Z a < uint.Z b ↔ a.toNat < b.toNat := by
      intro a b; simp [uint.Z]
    by_cases h1 : x.toNat < y.toNat
    · rw [if_pos (hlt.2 (Or.inl ((hz x y).2 h1))), if_pos h1]; decide
    · by_cases h2 : y.toNat < x.toNat
      · have : ¬ go.GoStringLt (x :: xs) (y :: ys) := by
          rw [hlt]; rintro (h | ⟨rfl, -⟩)
          · exact h1 ((hz x y).1 h)
          · omega
        rw [if_neg this, if_neg (by intro h; cases h; omega), if_neg h1, if_pos h2]; decide
      · have hxy : x = y := BitVec.eq_of_toNat_eq (by omega)
        subst hxy
        rw [if_neg h1, if_neg h2]
        have e1 : go.GoStringLt (x :: xs) (x :: ys) ↔ go.GoStringLt xs ys := by
          rw [hlt]; simp
        simp only [e1, List.cons.injEq, _root_.true_and]
        exact ih

end fpL

/-! ## Path elements and their lists -/

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace fpL

theorem isFieldsL_canon : ∀ (fs : List value.Field) (fl : FieldList),
    isFieldsL (GF := GF) fs fl ⊢ ⌜fl.all (fun f => f.2.canon) = true⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold isFieldsL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isFieldsL; iintro %h; exact h.elim
  | f :: fs, (n, x) :: rest => by
    unfold isFieldsL
    iintro ⟨-, Hv, Hr⟩
    ihave %h1 := valCanon _ _ _ $$ Hv
    ihave %h2 := isFieldsL_canon fs rest $$ Hr
    ipureintro
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨h1, h2⟩

theorem isPE_wf' (e : fieldpath.PathElement) (pe : PE) : isPE (GF := GF) e pe ⊢ ⌜pe.wf = true⌝ := by
  cases pe with
  | field n => iintro _; ipureintro; rfl
  | index i => iintro _; ipureintro; rfl
  | key fl =>
    unfold isPE isFieldList
    iintro ⟨-, %s, -, %fs, -, Hfs⟩
    ihave %h := isFieldsL_canon fs fl $$ Hfs
    ipureintro; exact h
  | value x =>
    unfold isPE
    iintro ⟨-, %v, -, Hv⟩
    ihave %h := valCanon _ _ _ $$ Hv
    ipureintro; exact h

theorem isPE_null (e : fieldpath.PathElement) (pe : PE) : isPE (GF := GF) e pe ⊢
    ⌜match pe with
     | .field _ => e.FieldName' ≠ null
     | .key _ => e.FieldName' = null ∧ e.Key' ≠ null
     | .value _ => e.FieldName' = null ∧ e.Key' = null ∧ e.Value' ≠ null
     | .index _ => e.FieldName' = null ∧ e.Key' = null ∧ e.Value' = null ∧ e.Index' ≠ null⌝ := by
  cases pe <;> unfold isPE
  · iintro H; iapply typedPointsto_not_null; iexact H
  · iintro ⟨%h, %s, H, -⟩
    ihave %h' := typedPointsto_not_null $$ H
    ipureintro; exact ⟨h, h'⟩
  · iintro ⟨%h, %v, H, -⟩
    ihave %h' := typedPointsto_not_null $$ H
    ipureintro; exact ⟨h.1, h.2, h'⟩
  · iintro ⟨%h, H⟩
    ihave %h' := typedPointsto_not_null $$ H
    ipureintro; exact ⟨h.1, h.2.1, h.2.2, h'⟩

theorem isPE_agree' (e : fieldpath.PathElement) (a b : PE) :
    isPE (GF := GF) e a ∗ isPE e b ⊢ ⌜a = b⌝ := by
  iintro ⟨Ha, Hb⟩
  ihave %na := isPE_null e a $$ Ha
  ihave %nb := isPE_null e b $$ Hb
  cases a <;> cases b <;> simp only at na nb <;> try (exfalso; simp_all; done)
  · unfold isPE; icombine Ha Hb gives %h; ipureintro; rw [h]
  · unfold isPE
    icases Ha with ⟨-, %s, Hs, Hfl⟩
    icases Hb with ⟨-, %s', Hs', Hfl'⟩
    icombine Hs Hs' gives %h; subst h
    ihave %h := flAgree _ _ _ $$ [$Hfl $Hfl']
    ipureintro; rw [h]
  · unfold isPE
    icases Ha with ⟨-, %v, Hs, Hv⟩
    icases Hb with ⟨-, %v', Hs', Hv'⟩
    icombine Hs Hs' gives %h; subst h
    ihave %h := valAgree _ _ _ _ _ $$ [$Hv $Hv']
    ipureintro; rw [h]
  · unfold isPE
    icases Ha with ⟨-, Hs⟩
    icases Hb with ⟨-, Hs'⟩
    icombine Hs Hs' gives %h; ipureintro; rw [h]

theorem isPEL_nil_eq : isPEL (GF := GF) [] [] = iprop(True) := by simp only [isPEL]

theorem isPEL_cons_eq (e : fieldpath.PathElement) (es : List fieldpath.PathElement) (pe : PE)
    (p : Path) : isPEL (GF := GF) (e :: es) (pe :: p) = iprop(isPE e pe ∗ isPEL es p) := by
  simp only [isPEL]

theorem isPEL_length : ∀ (es : List fieldpath.PathElement) (p : Path),
    isPEL (GF := GF) es p ⊢ ⌜es.length = p.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | [], _ :: _ => by unfold isPEL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isPEL; iintro %h; exact h.elim
  | e :: es, pe :: p => by
    unfold isPEL; iintro ⟨-, H⟩
    ihave %h := isPEL_length es p $$ H
    ipureintro; simp [h]

theorem isPEL_app : ∀ (es es' : List fieldpath.PathElement) (p p' : Path), es.length = p.length →
    (isPEL (GF := GF) (es ++ es') (p ++ p') ⊣⊢ isPEL es p ∗ isPEL es' p')
  | [], es', [], p', _ => by
    simp only [List.nil_append, isPEL_nil_eq]
    exact ⟨by iintro H; iframe H, by iintro ⟨-, H⟩; iexact H⟩
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | e :: es, es', pe :: p, p', h => by
    simp only [List.cons_append]
    have ih := isPEL_app es es' p p' (by simpa using h)
    simp only [isPEL_cons_eq]
    constructor
    · iintro ⟨He, H⟩
      icases ih.1 $$ H with ⟨H1, H2⟩
      iframe
    · iintro ⟨⟨He, H1⟩, H2⟩
      iframe
      iapply ih.2; iframe

theorem isPEL_wf : ∀ (es : List fieldpath.PathElement) (p : Path),
    isPEL (GF := GF) es p ⊢ ⌜∀ x ∈ p, x.wf = true⌝
  | [], [] => by iintro _; ipureintro; simp
  | [], _ :: _ => by unfold isPEL; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isPEL; iintro %h; exact h.elim
  | e :: es, pe :: p => by
    unfold isPEL; iintro ⟨He, H⟩
    ihave %h1 := isPE_wf' e pe $$ He
    ihave %h2 := isPEL_wf es p $$ H
    ipureintro; intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h2 x hx

/-- The element at an index. -/
theorem isPEL_lookup : ∀ (es : List fieldpath.PathElement) (p : Path) (k : Nat) (e : fieldpath.PathElement),
    es[k]? = some e → isPEL (GF := GF) es p ⊢ ∃ pe, ⌜p[k]? = some pe⌝ ∗ isPE e pe
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold isPEL; iintro %h; exact h.elim
  | e' :: es, pe :: p, 0, e, h => by
    simp at h; subst h
    unfold isPEL; iintro ⟨He, -⟩; iexists pe; iframe; ipureintro; rfl
  | e' :: es, pe :: p, k + 1, e, h => by
    simp at h
    rw [isPEL_cons_eq]; iintro ⟨-, H⟩
    simp only [List.getElem?_cons_succ]
    iapply isPEL_lookup es p k e h; iexact H

theorem isPEL_take_drop (es : List fieldpath.PathElement) (p : Path) (k : Nat) :
    isPEL (GF := GF) es p ⊢ isPEL (es.take k) (p.take k) ∗ isPEL (es.drop k) (p.drop k) := by
  iintro H
  ihave %hl := isPEL_length es p $$ H
  iapply (isPEL_app (es.take k) (es.drop k) (p.take k) (p.drop k) (by simp [hl])).1
  rw [List.take_append_drop, List.take_append_drop]; iexact H

end fpL

end rep

/-! ## The representation laws of `Vocab.lean` -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isPE_wf_law_holds : isPE_wf.law (GF := GF) := fun e pe => fpL.isPE_wf' e pe
theorem isPE_agree_law_holds : isPE_agree.law (GF := GF) := fun e a b => fpL.isPE_agree' e a b

theorem isPEs_persistent_law_holds : isPEs_persistent.law (GF := GF) := by
  intro es p; unfold isPEs; iintro #H; iexact H
theorem isPEs_nil_law_holds : isPEs_nil.law (GF := GF) := by
  unfold isPEs_nil.law isPEs; rw [fpL.isPEL_nil_eq]
theorem isPEs_cons_law_holds : isPEs_cons.law (GF := GF) := by
  intro e es pe p; unfold isPEs; rw [fpL.isPEL_cons_eq]; exact .rfl
theorem isPEs_app_law_holds : isPEs_app.law (GF := GF) := by
  intro es es' p p' h; unfold isPEs; exact fpL.isPEL_app es es' p p' h
theorem isPEs_length_law_holds : isPEs_length.law (GF := GF) := by
  intro es p; unfold isPEs; exact fpL.isPEL_length es p

theorem isPath_isPathF_law_holds : isPath_isPathF.law (GF := GF) := by
  intro s p; unfold isPath isPathF isPEs; exact .rfl

theorem isPathF_persist_law_holds : isPathF_persist.law (GF := GF) := by
  intro s dq p
  unfold isPath isPathF isPEs
  iintro ⟨%es, Hs, #H⟩
  imod ownSlice_persist $$ Hs with Hs
  imodintro
  iexists es; iframe; iexact H

instance isPESetV_pers (v : fieldpath.PathElementSet) (S : FSet PE) :
    Persistent (isPESetV (GF := GF) v DFrac.discard S) := by
  unfold isPESetV; infer_instance
instance isNodesV_pers (m : fieldpath.SetNodeMap) (D : PathSet) :
    Persistent (isNodesV (GF := GF) m D) := by
  unfold isNodesV; infer_instance
instance isNodes_pers (l : Loc) (D : PathSet) : Persistent (isNodes (GF := GF) l D) := by
  unfold isNodes; infer_instance
instance isPESet_pers (l : Loc) (S : FSet PE) : Persistent (isPESet (GF := GF) l DFrac.discard S) := by
  unfold isPESet; infer_instance

theorem isPESetV_persistent_law_holds : isPESetV_persistent.law (GF := GF) := by
  intro v S; iintro #H; iexact H

theorem isNodes_persistent_law_holds : isNodes_persistent.law (GF := GF) := by
  intro l D; iintro #H; iexact H

theorem ownPESetV_read_law_holds : ownPESetV_read.law (GF := GF) := by
  intro v S
  unfold ownPESetV isPESetV
  iintro ⟨%es, %xs, Hs, Hcap, #Hl, %h⟩
  iexists (DFrac.own 1)
  isplitl [Hs]
  · iexists es, xs; iframe; isplit; iexact Hl; ipureintro; exact h
  · iintro ⟨%es', %xs', Hs', #Hl', %h'⟩
    iexists es', xs'; iframe; isplit; iexact Hl'; ipureintro; exact h'

theorem ownPESetV_persist_law_holds : ownPESetV_persist.law (GF := GF) := by
  intro v S
  unfold ownPESetV isPESetV
  iintro ⟨%es, %xs, Hs, -, #Hl, %h⟩
  imod ownSlice_persist $$ Hs with Hs
  imodintro
  iexists es, xs; iframe; isplit; iexact Hl; ipureintro; exact h

theorem ownPESetV_zero_law_holds : ownPESetV_zero.law (GF := GF) := by
  unfold ownPESetV_zero.law ownPESetV
  iintro _
  iexists [], []
  isplitl
  · iapply ownSlice_nil
  isplitl
  · iapply ownSliceCap_nil
  rw [fpL.isPEL_nil_eq]
  isplit
  · itrivial
  · ipureintro; exact ⟨List.Pairwise.nil, rfl⟩

theorem isVSet_concrete_law_holds : isVSet_concrete.law (GF := GF) := by
  intro i e
  unfold isVSet
  iintro ⟨%p, %h, -⟩
  iexists _; ipureintro; exact h

theorem isValF_isValuePtr_law_holds : isValF_isValuePtr.law (GF := GF) := by
  intro v dq x
  unfold isValF
  iintro ⟨%p, %i, %h, -⟩
  ipureintro; exact ⟨p, h⟩

end laws

end smd
end EtcdGrove
end Perennial
