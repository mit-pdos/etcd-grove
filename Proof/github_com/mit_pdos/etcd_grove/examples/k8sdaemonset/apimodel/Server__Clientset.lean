/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__Clientset.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__Clientset

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

theorem Server.Clientset.wp_proof : Server.Clientset.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg
  wp_start as #Hs
  iapply wp_fupd
  wp_auto
  iStructNamedSuffix «$r0» "_f"
  ipersist s_f
  ipersist admin_f
  imodintro
  iapply HΦ
  unfold clientsetAt
  iexists s
  iframe #

end proof

end apimodel
end EtcdGrove
end Perennial
