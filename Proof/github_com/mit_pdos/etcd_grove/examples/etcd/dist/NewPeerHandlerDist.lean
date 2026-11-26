/- Lean-first (no Rocq counterpart).

`etcdhttp.NewPeerHandler` on a member machine: an interim trust-boundary axiom (`notes/etcd-dist-plan.md`,
"Interim transport").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewPeerHandlerDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.Assumptions]

/-- **`etcdhttp.NewPeerHandler(lg, s)` on a started member** (interim trust boundary). What it asserts of etcd
v3.6's `NewPeerHandler` (`etcdhttp/peer.go`): it returns (no panic, no stuck thread, no thread started) an
`http.Handler` `h`, etcd's peer handler of `s` (`peerHandlerOf h s`, opaque: only `PeerServe_dist` uses it).

Why it is true: `NewPeerHandler` is `newPeerHandler(lg, s, s.RaftHandler(), s.LeaseHandler(), s.HashKVHandler(),
s.DowngradeEnabledHandler())`, which reads fields `NewServer` set and no thread writes afterwards (the transport's,
`srvNetMember`; the lessor, the KV, the cluster: `isServerReqM`'s server), allocates the handlers and an
`http.ServeMux`, and registers fixed patterns (`/`, `/raft`, `/raft/`, `/members`, `/members/promote/`,
`/leases`, `/leases/internal`, `/members/hashkv`, `/downgrade/enabled`, `/version`): distinct patterns, so
`ServeMux.Handle` does not panic. Nothing is served yet.

Retired by the translation of `etcdhttp` (names only today) and its proof over S5's mux. -/
axiom NewPeerHandler_dist.wp_proof : NewPeerHandler_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial

end
