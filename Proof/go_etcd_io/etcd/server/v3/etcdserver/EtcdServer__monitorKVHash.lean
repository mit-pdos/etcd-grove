/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorKVHash.lean`: `s.monitorKVHash()` (`server.go`) with the check off: `s.Cfg.CorruptCheckTime` is zero and it returns at once. Until
prove-etcdserver (2026-11-20) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorKVHash

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

theorem EtcdServer.monitorKVHash.wp_proof :
    EtcdServer.monitorKVHash.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Ht
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
