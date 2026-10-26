/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__RemoveAllPeers.lean`:
`(*rafthttp.Transport).RemoveAllPeers()`. Unfinished (`sorry`, on purpose: the user's decision,
2026-10-25): the membership track's M5 proves it over the transport's lock (as `Stop_core`, with
the peers' stop rights of `trStopInv` and `removePeer`'s map deletions).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__RemoveAllPeers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.RemoveAllPeers.wp_proof :
    rafthttp.Transport.RemoveAllPeers.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
