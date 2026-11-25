/- Lean-first (no Rocq counterpart).

etcd's peer handler served on a member machine's peer listener: an interim trust-boundary axiom
(`notes/etcd-dist-plan.md`, "Interim transport").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PeerServeDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **etcd's peer handler served at the member's peer address** (interim trust boundary). What it asserts of Go
1.27's `http.Serve` (`&http.Server{Handler: h}`'s `Serve(pl)`) and etcd v3.6's peer handler over the net
extension: serving `pl` (accepting each connection and serving its requests on a goroutine of its own, until
`Accept` fails) neither gets stuck nor panics, whatever arrives at `pa`, and returns an error (`Serve` returns only
on one); its post is `True`.

Why it is true: every connection to `pa` is a dial at an address whose protocols are `httpPeerSvc`'s (opaque): its
bytes are written by another member's transport inside `NewServer_dist` (requests of etcd's peer API: rafthttp's
streams (`GET /raft/stream/...`), pipelines (`POST /raft`), probes (`GET /raft/probing`), snapshots
(`POST /raft/snapshot`); leasehttp's forwarded `TimeToLive` and `KeepAlive` (`POST /leases`, `/leases/internal`);
bootstrap's `GET /members`; `GET /version`), or by a program holding `httpAddrAt γ id pa`, which may dial `pa` and can write nothing there through the net
extension (no proof establishes the dialer protocol of any bytes); no HTTP proxy relays to it (`noProxyEnv` in
`NewServer_dist`). The names-only `leasehttp.RenewHTTP` axiom (and `promoteHTTPOk`) lets any program `POST`
a `LeaseKeepAliveRequest` body, with only a `Content-Type` header, to any URL, `pa`'s paths included (found by the
axiom review of 2026-11-24, `notes/etcd-dist-plan.md` §16.3). This axiom is sound against every request of that
shape (route B, 2026-11-25; fresh `axiom`-skill review: survives): rafthttp's paths refuse it (`412`: no
`X-Etcd-Cluster-ID` or version header, `rafthttp/http.go:471-516`); the GET-only paths answer `405`; `/leases` renews a
lease (the checkpointer off: no raft entry); `/leases/internal` dereferences a nil `LeaseTimeToLiveRequest`
(`lease/leasehttp/http.go:123`, before any lock), which `conn.serve` recovers; `/members/promote/<id>` proposes a
promotion only of an id in raft's progress (`isLearnerReady`, `server.go:1589-1611`: the static configuration), an
`AddNode` whose context has `IsPromote`, which the committed log's policy admits (`ccApplyOk`'s second disjunct) and
which changes nothing: with `shouldApplyV3` its validation fails (`ErrMemberNotLearner`: every saved member is a
voter), replayed `PromoteMember(id, false)` writes no bucket (`examples/axiomcx/promotenobucket`). Go's `configure`
registers a waiter at that change's id, which no proved code observes (the server's invariant gives a committed conf
change's id no waiter, `reqWaitNone`); the apply's `Trigger` hands it the `confChangeResponse` it expects. A request
with arbitrary bytes and raft's headers is not of that shape (it could crash raft: `tocommit out of range`), and no
program can write one at `pa` (above). The other route the review found is closed
(2026-11-25): a single-process run holds both `addrUnset pa` (the net extension's start resources, inside
`netAddrFree pa`; to `http_addr_set`) and `httpProtoFree pa` (`goose_adequacy_start`),
and `http.reserve` now also spends `pa`'s pending set (`netAddrPend`), which `http_addr_set` needs, so no program
holds both `httpAddrAt γ id pa` and a reservation of `pa` in the single-process registry (without it a one-process
program forged a raft message to its own member through rafthttp's round tripper; Go: `tocommit out of range`). The in-process `http.Serve_ok` with the raft handler
(`EtcdServer.RaftHandler.spec`, `srvServeRes`) is proved safe on what the in-process network carries
(`raftProto`), which is what these requests carry across machines: raft's messages of the cluster's members, each
checked by the handler (the cluster id, `X-Raft-To` against the member's id, a removed sender refused). The other
paths are etcd's own: `/leases` waits on the server's apply wait, which `start` makes (hence `isServerReqM`: the
program serves after `Start`, as etcd's embed does); `/members` reads the cluster; `/members/promote` proposes a promotion
only when asked (above); `/members/hashkv` and
`/downgrade/enabled` are what the (off) monitors of the other members would call. Go's server answers a malformed
request with a 4xx and closes; a handler's panic is recovered by `conn.serve`.

Retired by phase 7 S5's server half over the net extension (`Server.Serve` proved over its body; landed on `lean`
for the Net part) with the translation of `etcdhttp`, `leasehttp` and rafthttp's handlers, over S5's address facts. -/
axiom PeerServe_dist.wp_proof : PeerServe_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial

end
