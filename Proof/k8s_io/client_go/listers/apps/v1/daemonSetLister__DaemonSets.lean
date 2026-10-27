/-
Proof of `Spec/k8s_io/client_go/listers/apps/v1/daemonSetLister__DaemonSets.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetLister__DaemonSets
public import Spec.k8s_io.client_go.listers.NewNamespaced

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers.apps.v1

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]

theorem daemonSetLister.DaemonSets.wp_proof
    (wp_NewNamespaced : listers.NewNamespaced.spec (GF := GF) (hG := hG)) :
    daemonSetLister.DaemonSets.spec (GF := GF) (hG := hG) := by
  intro s dq ri ns
  wp_start as Hs
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNamespaced
  (try wp_auto)
  iapply HΦ
  iexact Hs

end proof

end appslisters
end EtcdGrove
end Perennial
