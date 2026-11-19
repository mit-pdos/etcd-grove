/-
`state.check`: `value.Equals` of the stored object and the expected one, and
`ManagedFields.Equals` of the managers, both true by the premise (the state's pieces persistent:
`*_persistent`). Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__check
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist

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

theorem state.check.wp_proof_of
    (hTVP : isTV_persistent.law (GF := GF)) (hMFP : isMF_persistent.law (GF := GF))
    (wp_AsValue_ptr : smd.typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_Equals : smd.value.Equals.spec (GF := GF))
    (wp_MFEquals_ptr : smd.fieldpath.ManagedFields.Equals_ptr.spec (GF := GF)) :
    state.check.spec (GF := GF) := fun s sc st m kvs mfm mf msg => by
  wp_start as ⟨Hst, Hm, Hmf, %h⟩
  obtain ⟨hlive, hmf⟩ := h
  unfold ownState
  icases Hst with ⟨%u, %lv, %mfm0, %cv, Hs, Hsc, Hu, Hcv, Hlv, Hmf0⟩
  ihave #Hlv := hTVP _ _ _ _ _ $$ Hlv
  ihave #Hmf0 := hMFP _ _ $$ Hmf0
  ihave #Hmf := hMFP _ _ $$ Hmf
  wp_auto
  wp_apply (wp_AsValue_ptr lv sc sc0 rootRef st.live) as %v Hv
  · iexact Hlv
  wp_apply (wp_NewValueInterface _ (.map kvs)) $$ [Hm] as %v' Hv'
  · unfold isUMap; iexact Hm
  wp_apply (wp_Equals v v' _ _ st.live (.map kvs)) $$ [Hv Hv'] as %r ⟨-, -, %hr⟩
  · iframe Hv Hv'
  have hr' : r = true := hr.2 hlive
  subst hr'
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %hsnn⟩
  iStructNamed Hs
  wp_apply (wp_MFEquals_ptr _ (DFrac.own 1) mfm0 mfm st.mf mf) $$ [managers] as %r ⟨%hr, managers⟩
  · iframe managers Hmf0 Hmf
  have hr' : r = true := hr.2 hmf
  subst hr'
  wp_auto
  iapply HΦ
  iexists u, lv, mfm0, cv
  iframe Hsc Hu Hcv Hlv Hmf0
  iapply typedPointsto_combine _ _ _ hsnn
  simp only [typedPointstoDef]
  iframe

theorem state.check.wp_proof
    (wp_AsValue_ptr : smd.typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_Equals : smd.value.Equals.spec (GF := GF))
    (wp_MFEquals_ptr : smd.fieldpath.ManagedFields.Equals_ptr.spec (GF := GF)) :
    state.check.spec (GF := GF) :=
  state.check.wp_proof_of isTV_persistent_law_holds isMF_persistent_law_holds wp_AsValue_ptr wp_NewValueInterface wp_Equals wp_MFEquals_ptr

end proof

end k8s_smd
end EtcdGrove
end Perennial
