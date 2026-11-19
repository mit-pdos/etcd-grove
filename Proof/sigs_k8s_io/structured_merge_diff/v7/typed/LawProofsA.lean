/-
**Proofs of `typed`'s representation and pool laws** (`WalkerLaws.lean`), part A: the package
fact (`typedPkgInit_pools`), the typed values (`isTV_isTVv`, `isTVu_isTVv`, persistence of
`isTVv`, `isComparison`, `outRep`), `isComparison_open`, `isValO_persist`, `spareWalkers_nil`,
and the five pools' zero walkers (`*_zero_pooled`).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import all Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The package fact -/

theorem typedPkgInit_pools_law_holds : typedPkgInit_pools.law (GF := GF) := by
  unfold typedPkgInit_pools.law
  have h := isPkgInit_access (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed
  with_unfolding_all exact h

/-! ## Typed values -/

instance isTVv_pers (tv : typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) :
    Persistent (isTVv (GF := GF) tv sc S t x) := by
  unfold isTVv; infer_instance

instance isComparison_pers (c : Loc) (C : Cmp) : Persistent (isComparison (GF := GF) c C) := by
  unfold isComparison; infer_instance

instance outRep_pers (o : Loc) (x : Option UVal) : Persistent (outRep (GF := GF) o x) := by
  cases x <;> unfold outRep <;> infer_instance

theorem isTV_isTVv_law_holds : isTV_isTVv.law (GF := GF) := fun p sc S t x => by
  unfold isTV isTVv
  constructor
  · iintro ⟨%v, %tr, #Hp, #Hv, #Htr, #Hsc, %Hc⟩
    iexists (typed.TypedValue.mk v tr sc)
    iframe #
    ipureintro; exact ⟨rfl, Hc⟩
  · iintro ⟨%tv, #Hp, %Hs, #Hv, #Htr, #Hsc, %Hc⟩
    iexists tv.value', tv.typeRef'
    cases tv
    simp only at Hs ⊢
    subst Hs
    iframe #
    ipureintro; exact Hc

theorem isTVu_isTVv_law_holds : isTVu_isTVv.law (GF := GF) := fun tv sc S t x => by
  unfold isTVu isTVv isVal
  constructor
  · iintro ⟨⟨%Hs, #Hv, #Htr, #Hsc, %Hw⟩, %Hc⟩
    iframe #
    ipureintro; exact ⟨Hs, Hw, Hc⟩
  · iintro ⟨%Hs, #Hv, #Htr, #Hsc, %Hw, %Hc⟩
    iframe #
    ipureintro; exact ⟨⟨Hs, Hw⟩, Hc⟩

theorem pers_box' {P : IProp GF} [Persistent P] : P ⊢ □ P := by
  iintro #H; imodintro; iexact H

theorem isTVv_persistent_law_holds : isTVv_persistent.law (GF := GF) :=
  fun _ _ _ _ _ => pers_box'
theorem isComparison_persistent_law_holds : isComparison_persistent.law (GF := GF) :=
  fun _ _ => pers_box'
theorem outRep_persistent_law_holds : outRep_persistent.law (GF := GF) :=
  fun _ _ => pers_box'

theorem isComparison_open_law_holds : isComparison_open.law (GF := GF) := fun c C => by
  unfold isComparison
  exact .rfl

theorem isValO_persist_law_holds : isValO_persist.law (GF := GF) := fun v dq o => by
  cases o with
  | none => unfold isValO; iintro %h; imodintro; ipureintro; exact h
  | some x => unfold isValO; exact isValF_persist_law_holds v dq x

/-! ## Walkers before a descent -/

theorem spareWalkers_nil_law_holds : spareWalkers_nil.law (GF := GF) := fun V _ => by
  unfold spareWalkers
  ileft; ipureintro; rfl

theorem ownPath_nil_law_holds : ownPath_nil.law (GF := GF) := by
  unfold ownPath_nil.law ownPath isPathF
  iintro
  isplitr
  · iexists []
    isplitr
    · iapply ownSlice_nil
    iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
    itrivial
  · iapply ownSliceCap_nil

/-! ## The pools' zero walkers -/

theorem mw_zero_pooled_law_holds : mw_zero_pooled.law (GF := GF) := fun w => by
  unfold mwPooled
  iintro Hw
  iexists _
  iframe Hw
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · iapply (show ⊢ ownPath (GF := GF) slice.nil [] from ownPath_nil_law_holds)
  isplitr
  · unfold spareWalkers; ileft; ipureintro; rfl
  ileft; ipureintro; rfl

theorem cw_zero_pooled_law_holds : cw_zero_pooled.law (GF := GF) := fun w => by
  unfold cwPooled
  iintro Hw
  iexists _
  iframe Hw
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply (show ⊢ ownPath (GF := GF) slice.nil [] from ownPath_nil_law_holds)
  isplitr
  · unfold spareWalkers; ileft; ipureintro; rfl
  ileft; ipureintro; rfl

theorem tw_zero_pooled_law_holds : tw_zero_pooled.law (GF := GF) := fun w => by
  unfold twPooled
  iintro Hw
  iexists _
  iframe Hw
  isplitr
  · ipureintro; rfl
  unfold spareWalkers
  ileft; ipureintro; rfl

theorem vw_zero_pooled_law_holds : vw_zero_pooled.law (GF := GF) := fun w => by
  unfold vwPooled
  iintro Hw
  iexists _
  iframe Hw
  isplitr
  · unfold spareWalkers; ileft; ipureintro; rfl
  ileft; ipureintro; rfl

theorem rw_zero_pooled_law_holds : rw_zero_pooled.law (GF := GF) := fun w => by
  unfold rwPooled
  iintro Hw
  iexists _
  iframe Hw
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  unfold spareWalkers
  ileft; ipureintro; rfl

end laws

end smd
end EtcdGrove
end Perennial
