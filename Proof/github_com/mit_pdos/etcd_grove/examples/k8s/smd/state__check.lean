/-
`state.check` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__check
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals_ptr
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Literals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.OwnLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem state.check.wp_proof
    (wp_AsValue_ptr : smd.typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_Equals : smd.value.Equals.spec (GF := GF))
    (wp_MFEquals_ptr : smd.fieldpath.ManagedFields.Equals_ptr.spec (GF := GF)) :
    state.check.spec (GF := GF) := fun s sc st m kvs mfm mf msg h => by
  -- the model: the stored object is `obj`, the managed fields are `managers`
  obtain ⟨x, hx, heq, hmf⟩ : ∃ x, st.live.value = some x ∧ UVal.equals x (.map kvs) = true ∧
      mfEquals st.mf mf = true := by
    simp only [stCheck, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hv : st.live.value with
    | none => simp [hv] at h1
    | some x => exact ⟨x, rfl, by simpa [hv] using h1, h2⟩
  wp_start as ⟨Hst, #Hm, #Hmf⟩
  unfold ownState
  icases Hst with ⟨%u, %lv, %mfm0, Hs, Hsc, #Hu, #Hlv, #Hmf0⟩
  wp_auto
  wp_apply (wp_AsValue_ptr lv sc st.live) as %v #Hv
  · iexact Hlv
  rw [hx]
  ihave #HmU := ownU_map m kvs $$ Hm
  wp_apply (wp_NewValueInterface (interface.mkOk mapStrIfaceTy #m) (.map kvs)) as %v' #Hv'
  · iexact HmU
  wp_apply (wp_Equals v v' x (.map kvs))
  · simp only [ownValueOpt]
    isplitr
    · iexact Hv
    · iexact Hv'
  rw [heq]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %hsnn⟩
  iStructNamed Hs
  wp_apply (wp_MFEquals_ptr _ (DFrac.own 1) mfm0 mfm st.mf mf) $$ [managers] as managers
  · iframe
    isplitr
    · iexact Hmf0
    · iexact Hmf
  rw [hmf]
  wp_auto
  iapply HΦ
  iexists u, lv, mfm0
  iframe
  isplitl [sc updater live managers]
  · iapply typedPointsto_combine _ _ _ hsnn
    simp only [typedPointstoDef]
    iframe
  iframe #

end proof

end k8s_smd
end EtcdGrove
end Perennial
