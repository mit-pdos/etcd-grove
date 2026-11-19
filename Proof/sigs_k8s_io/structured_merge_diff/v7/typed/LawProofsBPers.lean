/-
**Persistence instances of the merge walker's vocabulary** (`Walkers.lean`): what the merging and
compare walkers' proofs keep in the intuitionistic context.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs

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

instance ruleKeepRHSOk_pers (f : GoFunc) : Persistent (ruleKeepRHSOk (GF := GF) f) := by
  unfold ruleKeepRHSOk; infer_instance

instance outRep_pers (o : Loc) : (x : Option UVal) → Persistent (outRep (GF := GF) o x)
  | none => by unfold outRep; infer_instance
  | some _ => by unfold outRep; infer_instance

/-- A side is nil exactly when absent. -/
theorem isValO_nil (v : value.Value) (dq : DFrac) (o : Option UVal) :
    isValO (GF := GF) v dq o ⊢ isValO v dq o ∗ ⌜v = interface.nil ↔ o = none⌝ := by
  cases o with
  | none =>
    unfold isValO
    iintro %H
    isplitl; · ipureintro; exact H
    ipureintro; simp [H]
  | some x =>
    unfold isValO isValF
    iintro ⟨%p, %i, %Hv, Hp, Hi⟩
    isplitl
    · iexists p, i; iframe; ipureintro; exact Hv
    ipureintro
    subst Hv
    simp only [reduceCtorEq]

/-- A present side is a `*valueUnstructured`. -/
theorem isValO_some (v : value.Value) (dq : DFrac) (x : UVal) :
    isValO (GF := GF) v dq (some x) ⊢ isValO v dq (some x) ∗
      ⌜∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ := by
  unfold isValO isValF
  iintro ⟨%p, %i, %Hv, Hp, Hi⟩
  isplitl
  · iexists p, i; iframe; ipureintro; exact Hv
  ipureintro; exact ⟨p, Hv⟩

/-- No errors: the nil slice. -/
theorem errsIff_nil (ok : Prop) (h : ok) : ⊢ errsIff (GF := GF) slice.nil ok := by
  unfold errsIff ownErrs
  iexists []
  isplitl
  · isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · ipureintro; exact ⟨fun _ => h, fun _ => rfl⟩

theorem noErrs_nil : ⊢ noErrs (GF := GF) slice.nil := by
  unfold noErrs ownErrs
  isplitl
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil

/-- An empty errors slice has length 0. -/
theorem noErrs_len (s : GoSlice) : noErrs (GF := GF) s ⊢ ⌜sint.Z s.len = 0⌝ := by
  unfold noErrs ownErrs
  iintro ⟨Hs, _⟩
  ihave %H := ownSlice_len _ _ _ $$ Hs
  ipureintro
  obtain ⟨h1, h2⟩ := H
  simp only [List.length_nil] at h1
  word

/-- Calling `ruleKeepRHS`'s closure (the persistent spec read at one call). -/
theorem ruleKeepRHSOk_call (f : GoFunc) (w : Loc) (v : typed.mergingWalker) (dql dqr : DFrac)
    (l r : Option UVal) :
    ruleKeepRHSOk (GF := GF) f ⊢
    {{ w ↦ v ∗ isValO v.lhs' dql l ∗ isValO v.rhs' dqr r ∗ ⌜l.isSome ∨ r.isSome⌝ }}
      (App (Val #f) (Val #w))
    {{ RET #(); ∃ o : Loc, w ↦ { v with out' := o } ∗ outRep o (leafM l r) ∗
        isValO v.lhs' dql l ∗ isValO v.rhs' dqr r }} := by
  unfold ruleKeepRHSOk
  iintro #H
  iapply H

end laws

end smd
end EtcdGrove
end Perennial
