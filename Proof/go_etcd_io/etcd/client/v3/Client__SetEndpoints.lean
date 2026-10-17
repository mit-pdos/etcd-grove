/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__SetEndpoints.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__SetEndpoints
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__SetEndpoints

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.SetEndpoints.wp_proof
    (wp_rSetEndpoints : resolver.EtcdManualResolver.SetEndpoints.spec (GF := GF) (hG := hG)) :
    Client.SetEndpoints.spec (GF := GF) (hG := hG) := by
  intro c mu r esl0 eps0 sl eps
  wp_start as ⟨#Hmu, #Hguard, Heps, #Hr, Hro, #Hsl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hres : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hguard] as ⟨Hwl, -⟩
  wp_apply wp_rSetEndpoints r eps0 sl eps $$ [$Hres $Hro $Hsl] as Hro
  wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
