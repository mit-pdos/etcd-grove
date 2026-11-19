/-
`state.typedObj` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped
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

theorem state.typedObj.wp_proof
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_AsTyped : smd.typed.AsTyped.spec (GF := GF)) :
    state.typedObj.spec (GF := GF) := fun s sc u lv mfm m kvs hval => by
  wp_start as ⟨Hs, Hsc, #Hm⟩
  wp_auto
  ihave #HmU := ownU_map m kvs $$ Hm
  wp_apply (wp_NewValueInterface (interface.mkOk mapStrIfaceTy #m) (.map kvs)) as %v #Hv
  · iexact HmU
  ipersist rootName
  wp_apply (wp_AsTyped v (.map kvs) sc k8s_smd.sc _ rootRef rfl (by decide +kernel)) $$ [Hsc]
    as %p %err ⟨Hsc, Hp⟩
  · iframe
    isplitr
    · iexact Hv
    unfold rootRef
    iapply ownTypeRef_named
    iexact rootName
  have hA : asTyped k8s_smd.sc (UVal.map kvs) rootRef = some ⟨some (.map kvs), rootRef⟩ := by
    simp [asTyped, hval]
  rw [hA]
  icases Hp with ⟨%herr, #Hp⟩
  subst herr
  wp_auto
  iapply HΦ
  iframe Hp
  iframe

end proof

end k8s_smd
end EtcdGrove
end Perennial
