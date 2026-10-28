/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/IsPodReady.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodReady
public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.IsPodReadyConditionTrue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

theorem IsPodReady.wp_proof
    (wp_IsPodReadyConditionTrue : IsPodReadyConditionTrue.spec (GF := GF) (hG := hG)) :
    IsPodReady.spec (GF := GF) (hG := hG) := by
  intro pod dq d
  wp_start as Hp
  iunfold podAt at Hp
  icases Hp with ⟨%v, Hl, Hd⟩
  icases pod_conds_acc v dq d $$ Hd with ⟨Hc, Hd⟩
  wp_auto
  icases (AccessStrict.access_strict
      (A := pod.[k8s_io.api.core.v1.Pod, go!"Status"] ↦{dq} v.Status')
      (A' := pod.[k8s_io.api.core.v1.Pod, go!"Status"] ↦{dq} v.Status')
      (P := pod ↦{dq} v)) $$ Hl with ⟨Hf, Hl⟩
  wp_auto
  ihave Hl := Hl $$ Hf
  wp_apply (wp_IsPodReadyConditionTrue v.Status' dq d.Status'.Conditions') $$ [$Hc] as Hc
  iapply HΦ
  iunfold podAt
  iexists v
  iframe Hl
  iapply Hd $$ Hc

end proof

end dsctl
end EtcdGrove
end Perennial
