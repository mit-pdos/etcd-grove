/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__AdminClientset.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__AdminClientset

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

theorem Server.AdminClientset.wp_proof : Server.AdminClientset.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg
  wp_start as #Hs
  wp_auto
  wp_apply +noauto wp_alloc as %c Hc
  iStructNamedSuffix Hc "_f"
  ipersist s_f
  ipersist admin_f
  wp_auto
  iapply HΦ
  unfold clientsetAt
  iexists s
  iframe #

end proof

end apimodel
end EtcdGrove
end Perennial
