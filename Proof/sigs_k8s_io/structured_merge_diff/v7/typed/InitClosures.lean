/-
**The closures of `typed`'s package fact** (`typedPools`, `Base.lean`; `Closures.lean`): each
pool's `New` makes a pooled walker (`sync.newSpec`, from the `*_zero_pooled` laws), and
`ruleKeepRHS`'s closure meets `ruleKeepRHSOk` (over `Value.Unstructured`'s spec on the one
dynamic type in scope, `*valueUnstructured`: `isValF_concrete`). What the generated initializer
(`etc/gen-init.py`, `InitLinked.lean`) proves the fact with.

Prove phase (2026-11-19, notes/smd-plan.md, "Draft integrated").
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Closures
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section closures
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-! ## The pools' `New` -/

/-- A pool literal `sync.Pool{New: f}` stored at `p` becomes an `isPool` of `New`'s values. -/
theorem init_typedPool (P : GoAny → IProp GF) (f : GoFunc)
    (hN : ⊢ sync.newSpec f iprop(True) P) (p : Loc) (v : sync.Pool) :
    p ↦ v ∗ ⌜v.local' = null ∧ v.New' = f⌝ ⊢ |={⊤}=> sync.isPool p f iprop(True) P := by
  iintro ⟨Hp, %h⟩
  obtain ⟨hl, hf⟩ := h
  subst hf
  iapply sync.init_Pool p v iprop(True) P ⊤ hl
  iframe Hp
  iapply hN

theorem wp_mwNewV :
    {{ True }} (App (Val #typed.mwNewV) (Val #()))
    {{ (x : GoAny), RET #x; pooledAs (GF := GF) typed.mergingWalker.ty mwPooled x }} := by
  wp_start as _
  rw [typed.mwNewV_val]
  wp_auto
  wp_apply wp_alloc as %w Hw
  try wp_auto
  iapply HΦ
  unfold pooledAs
  iexists w
  isplitr
  · ipureintro; rfl
  iapply (mw_zero_pooled_law_holds w) $$ Hw

theorem newSpec_mwNewV (R : IProp GF) :
    ⊢ sync.newSpec typed.mwNewV R (pooledAs (GF := GF) typed.mergingWalker.ty mwPooled) := by
  iapply sync.newSpec_of_true
  iright
  iapply wp_mwNewV

theorem wp_cwNewV :
    {{ True }} (App (Val #typed.cwNewV) (Val #()))
    {{ (x : GoAny), RET #x; pooledAs (GF := GF) typed.compareWalker.ty cwPooled x }} := by
  wp_start as _
  rw [typed.cwNewV_val]
  wp_auto
  wp_apply wp_alloc as %w Hw
  try wp_auto
  iapply HΦ
  unfold pooledAs
  iexists w
  isplitr
  · ipureintro; rfl
  iapply (cw_zero_pooled_law_holds w) $$ Hw

theorem newSpec_cwNewV (R : IProp GF) :
    ⊢ sync.newSpec typed.cwNewV R (pooledAs (GF := GF) typed.compareWalker.ty cwPooled) := by
  iapply sync.newSpec_of_true
  iright
  iapply wp_cwNewV

theorem wp_twNewV :
    {{ True }} (App (Val #typed.twNewV) (Val #()))
    {{ (x : GoAny), RET #x; pooledAs (GF := GF) typed.toFieldSetWalker.ty twPooled x }} := by
  wp_start as _
  rw [typed.twNewV_val]
  wp_auto
  wp_apply wp_alloc as %w Hw
  try wp_auto
  iapply HΦ
  unfold pooledAs
  iexists w
  isplitr
  · ipureintro; rfl
  iapply (tw_zero_pooled_law_holds w) $$ Hw

theorem newSpec_twNewV (R : IProp GF) :
    ⊢ sync.newSpec typed.twNewV R (pooledAs (GF := GF) typed.toFieldSetWalker.ty twPooled) := by
  iapply sync.newSpec_of_true
  iright
  iapply wp_twNewV

theorem wp_vwNewV :
    {{ True }} (App (Val #typed.vwNewV) (Val #()))
    {{ (x : GoAny), RET #x; pooledAs (GF := GF) typed.validatingObjectWalker.ty vwPooled x }} := by
  wp_start as _
  rw [typed.vwNewV_val]
  wp_auto
  wp_apply wp_alloc as %w Hw
  try wp_auto
  iapply HΦ
  unfold pooledAs
  iexists w
  isplitr
  · ipureintro; rfl
  iapply (vw_zero_pooled_law_holds w) $$ Hw

theorem newSpec_vwNewV (R : IProp GF) :
    ⊢ sync.newSpec typed.vwNewV R (pooledAs (GF := GF) typed.validatingObjectWalker.ty vwPooled) := by
  iapply sync.newSpec_of_true
  iright
  iapply wp_vwNewV

theorem wp_rwNewV :
    {{ True }} (App (Val #typed.rwNewV) (Val #()))
    {{ (x : GoAny), RET #x; pooledAs (GF := GF) typed.reconcileWithSchemaWalker.ty rwPooled x }} := by
  wp_start as _
  rw [typed.rwNewV_val]
  wp_auto
  wp_apply wp_alloc as %w Hw
  try wp_auto
  iapply HΦ
  unfold pooledAs
  iexists w
  isplitr
  · ipureintro; rfl
  iapply (rw_zero_pooled_law_holds w) $$ Hw

theorem newSpec_rwNewV (R : IProp GF) :
    ⊢ sync.newSpec typed.rwNewV R (pooledAs (GF := GF) typed.reconcileWithSchemaWalker.ty rwPooled) := by
  iapply sync.newSpec_of_true
  iright
  iapply wp_rwNewV

/-! ## `ruleKeepRHS` -/

/-- `isValF_concrete`, keeping the wrapper. -/
theorem isValF_concrete_keep (hC : isValF_concrete.law (GF := GF)) (v : value.Value) (dq : DFrac)
    (x : UVal) :
    isValF (GF := GF) v dq x ⊢ isValF v dq x ∗
      ⌜∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ := by
  refine pure_elim
    (∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p) ?_
    (fun h => ?_)
  · iintro H
    ihave ⟨%p, %h⟩ := hC v dq x $$ H
    ipureintro; exact ⟨p, h⟩
  · iintro H; iframe H; ipureintro; exact h

theorem ruleKeepRHSV_ok
    (hU : value.valueUnstructured.Unstructured_ptr.spec (GF := GF))
    (hC : isValF_concrete.law (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ⊢
      ruleKeepRHSOk (GF := GF) typed.ruleKeepRHSV := by
  iintro #Hpv
  unfold ruleKeepRHSOk
  imodintro
  iintro %w %wv %dql %dqr %l %r
  wp_start as ⟨Hw, Hl, Hr, %Hlr⟩
  iapply wp_fupd
  rw [typed.ruleKeepRHSV_val]
  wp_auto
  cases r with
  | none =>
    cases l with
    | none => simp at Hlr
    | some y =>
    simp only [isValO]
    icases Hr with %hr
    icases isValF_concrete_keep hC _ _ _ $$ Hl with ⟨Hl, %hp⟩
    obtain ⟨p, hp⟩ := hp
    rw [hr]
    wp_auto
    rw [hp]
    wp_auto
    rw [hp]
    wp_apply hU $$ [Hl] as %u ⟨Hl, #Hu⟩
    · iframe #; iframe
    wp_auto
    imod (typedPointsto_dfractional _ _).dfractional_persist _ $$ v with #Hv
    irevert Hw
    rw [hp, hr]
    iintro Hw
    imodintro
    iapply HΦ
    iexists _
    iframe Hw Hl
    isplitr
    · simp only [leafM, outRep]
      iexists u
      iframe #
    ipureintro; rfl
  | some x =>
    simp only [isValO]
    icases isValF_concrete_keep hC _ _ _ $$ Hr with ⟨Hr, %hp⟩
    obtain ⟨p, hp⟩ := hp
    rw [hp]
    wp_auto
    rw [hp]
    wp_apply hU $$ [Hr] as %u ⟨Hr, #Hu⟩
    · iframe #; iframe
    wp_auto
    imod (typedPointsto_dfractional _ _).dfractional_persist _ $$ v with #Hv
    irevert Hw
    rw [hp]
    iintro Hw
    imodintro
    iapply HΦ
    iexists _
    iframe Hw Hl Hr
    simp only [leafM, outRep]
    iexists u
    iframe #

end closures

end smd
end EtcdGrove
end Perennial
