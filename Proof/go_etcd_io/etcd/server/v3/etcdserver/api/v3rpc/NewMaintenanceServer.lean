/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewMaintenanceServer.lean` over the
real code (`maintenance.go`): `NewMaintenanceServer(s, hn)` reads `s.Cfg.Logger`, calls `s.KV()`
and the watchable store's `HashStorage()` (mvcc's API, at the store's `isMvcc`), `newHeader(s)`,
`etcdserver.NewServerVersionAdapter(s)` (an allocation, stepped into), possibly `zap.NewNop()`, and
allocates a `maintenanceServer`, an `AuthAdmin` and the `authMaintenanceServer` it returns.
Lean-first (no Rocq counterpart). Until 2026-11-21 a trust-boundary axiom (`version.Server` was
axiomatized by the translation).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewMaintenanceServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.NewMaintenanceServer.wp_proof
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hHS : mvcc.api.watchableStore.HashStorage.spec (GF := GF) (hG := hG))
    (hNH : v3rpc.newHeader.spec (GF := GF) (hG := hG))
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    v3rpc.NewMaintenanceServer.spec (GF := GF) (hG := hG) := by
  intro s A lg0 wsl hn γ
  wp_start as ⟨#Hkv, #Hlg, #Hkva, #Hmv⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply (hKV s (v3rpc.wsIface wsl))
  · iframe #
  (try wp_auto)
  wp_apply (hHS wsl γ) as %h -
  · iframe #
  (try wp_auto)
  wp_apply hNH $$ [] as %hv -
  · iframe #
  (try wp_auto)
  -- `etcdserver.NewServerVersionAdapter(s)`: an allocation
  wp_func_call
  wp_call
  (try wp_auto)
  wp_alloc adp as Hadp
  (try wp_auto)
  wp_if_destruct
  · wp_apply hNop as %l -
    (try wp_auto)
    wp_alloc q as Hq
    (try wp_auto)
    iapply HΦ
    iexists _
    ipureintro; rfl
  · (try wp_auto)
    wp_alloc q as Hq
    (try wp_auto)
    iapply HΦ
    iexists _
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
