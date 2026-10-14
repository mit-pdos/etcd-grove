/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/fillDefault.lean`.

`model` is a heap cell. `Partition` is `nil` (`isModel`): `noPartition` is stored. The other
`if`s on the `Describe*` and `PartitionEvent` defaults are joined (`wp_join`) at "the cell holds
a model that `Keep`s `m`'s `Init`, `Step`, `StepContext`, `Equal`, `Hash`"; `Equal` is not `nil`
(`isModel`). The `switch`: both `Step` and `StepContext` `nil` (the panic) is excluded by
`isModel`; `Step` `nil` stores a closure over `StepContext` in `Step` (no spec needed, `StepContext`
keeps its own); `StepContext` `nil` stores `func(ctx, ...) { return model.Step(...) }`, which
reads `Step` from the cell: the cell is persisted once stored (`ipersist`), and the closure's
`stepCtxSpec` follows from `Step`'s `stepSpec`.
-/
module

public import Spec.github_com.anishathalye.porcupine.fillDefault
public import Spec.github_com.anishathalye.porcupine.noPartition
public import Perennial.Spec.context.Background

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- What `fillDefault` keeps of the model `m` in `m1` (and the `Partition` it stores). -/
def Keep (m m1 : Model) : Prop :=
  m1.Partition' = functions github_com.anishathalye.porcupine.noPartition [] ∧
  m1.Init' = m.Init' ∧ m1.Step' = m.Step' ∧ m1.StepContext' = m.StepContext' ∧
  m1.Equal' = m.Equal' ∧ m1.Hash' = m.Hash'

/-- `noPartition`'s function value, as `fillDefault` stores it. -/
theorem noPartitionSpec_of (hNoPartition : noPartition.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ⊢
      noPartitionSpec (functions github_com.anishathalye.porcupine.noPartition []) := by
  iintro #Hpkg
  unfold noPartitionSpec
  iintro %sl %ops %dq
  iintro !> %Φ Hs HΦ
  wp_apply (hNoPartition sl ops dq) $$ [$Hs] as %r ⟨Hr, Hs⟩
  iapply HΦ
  iframe

/-- The model `fillDefault` returns, from what it keeps of `m` and the spec of its
`StepContext`. -/
theorem filled_of (hNoPartition : noPartition.spec (GF := GF) (hG := hG)) {σ : Type}
    (S : ModelSpec GF σ) (m m' : Model)
    (hP : m'.Partition' = functions github_com.anishathalye.porcupine.noPartition [])
    (hI : m'.Init' = m.Init') (hE : m'.Equal' = m.Equal') (hH : m'.Hash' = m.Hash') :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ initSpec S m.Init' ∗
      isEqHash S m ∗ stepCtxSpec S m'.StepContext' ⊢
      isModelFilled S m' ∗ noPartitionSpec m'.Partition' := by
  iintro ⟨#Hpkg, #Hinit, #Heh, #Hsc⟩
  unfold isModelFilled isEqHash
  rw [hP, hI, hE, hH]
  isplitl []
  · iframe #
  · iapply noPartitionSpec_of hNoPartition $$ Hpkg

theorem fillDefault.wp_proof
    (hNoPartition : noPartition.spec (GF := GF) (hG := hG))
    (hBackground : context.Background.spec (GF := GF) (hG := hG)) :
    fillDefault.spec (GF := GF) (hG := hG) :=
  fun σ S m => by
  wp_start as #Hm
  iunfold isModel at Hm
  icases Hm with ⟨%Hpart, #Hinit, #Hstep, #Heh⟩
  wp_auto
  wp_if_destruct
  rotate_left
  · exact absurd Hpart Hif
  wp_join (iprop(∃ m1 : Model, model_ptr ↦ m1 ∗ ⌜Keep (GF := GF) (hG := hG) m m1⌝) : IProp GF)
    with [model] as ⟨%m1, model, %Hk⟩
  · iexists _; iframe model; ipureintro; simp [Keep]
  · iexists _; iframe model; ipureintro; simp [Keep]
  ihave #Heh2 := Heh
  iunfold isEqHash at Heh2
  icases Heh2 with ⟨%HeqNil, -, -⟩
  wp_if_destruct
  · exact absurd (Hk.2.2.2.2.1 ▸ Hif) HeqNil
  wp_join (iprop(∃ m1 : Model, model_ptr ↦ m1 ∗ ⌜Keep (GF := GF) (hG := hG) m m1⌝) : IProp GF)
    with [model] as ⟨%m2, model, %Hk2⟩
  · iexists _; iframe model; ipureintro; simp only [Keep] at *; exact Hk
  · iexists _; iframe model; ipureintro; exact Hk
  wp_join (iprop(∃ m1 : Model, model_ptr ↦ m1 ∗ ⌜Keep (GF := GF) (hG := hG) m m1⌝) : IProp GF)
    with [model] as ⟨%m3, model, %Hk3⟩
  · iexists _; iframe model; ipureintro; simp only [Keep] at *; exact Hk2
  · iexists _; iframe model; ipureintro; exact Hk2
  wp_join (iprop(∃ m1 : Model, model_ptr ↦ m1 ∗ ⌜Keep (GF := GF) (hG := hG) m m1⌝) : IProp GF)
    with [model] as ⟨%m4, model, %Hk4⟩
  · iexists _; iframe model; ipureintro; simp only [Keep] at *; exact Hk3
  · iexists _; iframe model; ipureintro; exact Hk3
  obtain ⟨hP4, hI4, hS4, hSC4, hE4, hH4⟩ := Hk4
  icases Hstep with (⟨%HscNN, #Hsc⟩ | ⟨%HscN2, #Hst⟩)
  · rw [hS4]
    wp_if_destruct
    · -- `Step` nil: a closure over `StepContext`
      rw [hSC4]
      simp only [HscNN, decide_false]
      wp_auto
      simp only [hS4, Hif, _root_.decide_true]
      wp_auto
      wp_apply hBackground
      iapply HΦ
      iapply (filled_of hNoPartition S m _ ?hP ?hI ?hE ?hH)
      case hP => exact hP4
      case hI => exact hI4
      case hE => exact hE4
      case hH => exact hH4
      simp only
      rw [hSC4]
      iframe #
    · simp only [hS4, Hif, decide_false]
      wp_auto
      simp only [hSC4, HscNN, decide_false]
      wp_auto
      iapply HΦ
      iapply (filled_of hNoPartition S m _ ?hP ?hI ?hE ?hH)
      case hP => exact hP4
      case hI => exact hI4
      case hE => exact hE4
      case hH => exact hH4
      rw [hSC4]
      iframe #
  · rw [hS4]
    wp_if_destruct
    · exact absurd Hif HscN2.2
    simp only [hS4, Hif, decide_false]
    wp_auto
    simp only [hSC4, HscN2.1, _root_.decide_true]
    wp_pures
    wp_func_lits
    wp_store
    ipersist model
    wp_auto
    iapply HΦ
    iapply (filled_of hNoPartition S m _ ?hP ?hI ?hE ?hH)
    case hP => exact hP4
    case hI => exact hI4
    case hE => exact hE4
    case hH => exact hH4
    iframe #
    -- the closure `func(ctx, state, input, output) { return model.Step(state, input, output) }`
    simp only
    unfold stepCtxSpec
    iintro %c %v %st %i %o
    iintro !> %Φ' ⟨Hrep, Hio⟩ HΦ'
    ihave #M := model
    iStructNamedPrefix M "M"
    wp_auto
    rw [hS4]
    iunfold stepSpec at Hst
    wp_apply Hst $$ %v %st %i %o [$Hrep $Hio] as %ok %v' ⟨%Hok, Hpost⟩
    iapply HΦ'
    iframe
    ipureintro; exact Hok

end proof

end porcupine
end EtcdGrove
end Perennial
