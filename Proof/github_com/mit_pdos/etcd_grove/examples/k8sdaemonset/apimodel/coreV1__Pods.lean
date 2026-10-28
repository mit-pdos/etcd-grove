/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/coreV1__Pods.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Pods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem coreV1.Pods.wp_proof : coreV1.Pods.spec (GF := GF) (hG := hG) := by
  intro _ l γ cfg admin ns
  wp_start as Hl
  unfold coreV1At
  icases Hl with ⟨%s, #Hs, #Ha, #Hsrv⟩
  wp_auto
  wp_apply +noauto wp_alloc as %c Hc
  iStructNamedSuffix Hc "_f"
  ipersist s_f
  ipersist admin_f
  ipersist ns_f
  wp_auto
  iapply HΦ
  unfold isPodClient podClientAt
  iexists c
  isplitr
  · ipureintro; rfl
  iexists s
  iframe #

end proof

end apimodel
end EtcdGrove
end Perennial
