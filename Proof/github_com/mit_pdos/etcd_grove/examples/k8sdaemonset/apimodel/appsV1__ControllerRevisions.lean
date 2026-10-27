/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/appsV1__ControllerRevisions.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.appsV1__ControllerRevisions

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem appsV1.ControllerRevisions.wp_proof : appsV1.ControllerRevisions.spec (GF := GF) (hG := hG) := by
  intro l γ cfg admin ns
  wp_start as Hl
  unfold appsV1At
  icases Hl with ⟨%s, #Hs, #Ha, #Hsrv⟩
  wp_auto
  wp_apply +noauto wp_alloc as %c Hc
  iStructNamedSuffix Hc "_f"
  ipersist s_f
  ipersist admin_f
  ipersist ns_f
  wp_auto
  iapply HΦ
  unfold isCRClient crClientAt
  iexists c
  isplitr
  · ipureintro; rfl
  iexists s
  iframe #

end proof

end apimodel
end EtcdGrove
end Perennial
