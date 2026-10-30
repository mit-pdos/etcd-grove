/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.watcher__newWatcherGRPCStream
public import Spec.go_etcd_io.etcd.client.v3.streamKeyFromCtx
public import Spec.go_etcd_io.etcd.client.v3.OpWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas
public import Proof.go_etcd_io.etcd.client.v3.WatchFire

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watcher.Watch.wp_proof
    (wp_OpWatch : OpWatch.spec (GF := GF) (hG := hG))
    (wp_key : streamKeyFromCtx.spec (GF := GF) (hG := hG))
    (wp_newStream : watcher.newWatcherGRPCStream.spec (GF := GF) (hG := hG)) :
    watcher.Watch.spec (GF := GF) (hG := hG) := by
  -- the proof of the spec before G2: `git show 8527537fba:Proof/go_etcd_io/etcd/client/v3/watcher__Watch.lean`
  sorry -- G2: re-prove after freeze

end proof

end EtcdGrove
end Perennial
