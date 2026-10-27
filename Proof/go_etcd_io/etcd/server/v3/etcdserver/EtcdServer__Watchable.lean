/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Watchable.lean`. Lean-first (no Rocq
counterpart); the watch slice's unit W-S (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Watchable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Watchable.wp_proof (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG)) :
    EtcdServer.Watchable.spec (GF := GF) (hG := hG) := by
  intro s kv
  wp_start as #Hkv
  wp_auto
  wp_apply (hKV s kv)
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
