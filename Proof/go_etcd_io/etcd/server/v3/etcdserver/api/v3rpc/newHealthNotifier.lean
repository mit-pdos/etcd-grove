/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newHealthNotifier.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHealthNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.healthNotifier__startServe
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.newHealthNotifier.wp_proof
    (hStart : v3rpc.healthNotifier.startServe.spec (GF := GF) (hG := hG))
    (hLogger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hFE : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG)) :
    v3rpc.newHealthNotifier.spec (GF := GF) (hG := hG) := by
  intro hs s lg fg
  wp_start as ⟨%Hhs, #Hh, #Hlg, %Hlgn, Hlr, #Hfg, #Hgate⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · contradiction
  (try wp_auto)
  wp_apply (hLogger s lg) $$ [Hlr] as ⟨-, Hlr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply (hFE s fg _) as %b -
  · iframe #; ipureintro; simp [serverFeatures]
  (try wp_auto)
  iStructNamed «$r0»
  ipersist hs
  ipersist lg
  wp_apply (hStart «$r0_ptr» _ lg)
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
