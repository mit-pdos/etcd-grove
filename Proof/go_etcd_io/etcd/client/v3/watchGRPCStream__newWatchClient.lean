/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__newWatchClient.lean` (the watch slice's
unit W-C): `newWatchClient` at its first call. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__waitCancelSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__openWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveWatchClient
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Proof.go_etcd_io.etcd.client.v3.WatchRecon
public import Proof.go_etcd_io.etcd.client.v3.InvWcJoin

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

theorem watchGRPCStream.newWatchClient.wp_proof
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_wait : watchGRPCStream.waitCancelSubstreams.spec (GF := GF) (hG := hG))
    (wp_open : watchGRPCStream.openWatchClient.spec (GF := GF) (hG := hG))
    (wp_serve : watchGRPCStream.serveWatchClient.spec (GF := GF) (hG := hG))
    (wp_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG) := by
  -- the proof before G2: `git show 8527537fba:Proof/go_etcd_io/etcd/client/v3/watchGRPCStream__newWatchClient.lean`
  sorry -- G2: re-prove after freeze

end proof

end EtcdGrove
end Perennial
