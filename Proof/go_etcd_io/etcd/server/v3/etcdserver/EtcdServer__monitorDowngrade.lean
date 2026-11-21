/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorDowngrade.lean`: `s.monitorDowngrade()` (`server.go`) with the check off: it builds its monitor (`serverversion.NewMonitor(s.Logger(), NewServerVersionAdapter(s))`, two allocations, stepped into), reads `s.Cfg.DowngradeCheckTime`, zero, and returns. Until
prove-etcdserver (2026-11-20) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorDowngrade

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.monitorDowngrade.wp_proof :
    EtcdServer.monitorDowngrade.spec (GF := GF) (hG := hG) := by
  intro s l
  wp_start as ⟨#Hl, Hrd, #Ht⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvLgReader at Hrd
  icases Hrd with ⟨%mu, #Hmu, Hh⟩
  wp_auto
  -- `s.Logger()`, stepped into (its spec asks for `zapLoggerOk l`, which this call does not need)
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hlk, HP⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk] as Hh
  · inext; itrivial
  (try wp_auto)
  -- `NewServerVersionAdapter(s)`, then `serverversion.NewMonitor(lg, adapter)`: allocations
  wp_func_call
  wp_call
  (try wp_auto)
  wp_alloc adp as Hadp
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
