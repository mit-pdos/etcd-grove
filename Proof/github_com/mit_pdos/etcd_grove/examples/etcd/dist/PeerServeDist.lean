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
bootstrap's `GET /members`; `GET /version`), or by no one (a program holding `httpAddrAt pa` may dial `pa`, and can
write nothing there: no proof establishes the dialer protocol of any bytes; the client machines dial no peer address;
no HTTP proxy relays to it, `noProxyEnv` in `NewServer_dist`). The in-process `http.Serve_ok` with the raft handler
(`EtcdServer.RaftHandler.spec`, `srvServeRes`) is proved safe on what the in-process network carries
(`raftProto`), which is what these requests carry across machines: raft's messages of the cluster's members, each
checked by the handler (the cluster id, `X-Raft-To` against the member's id, a removed sender refused). The other
paths are etcd's own: `/leases` waits on the server's apply wait, which `start` makes (hence `isServerReqM`: the
program serves after `Start`, as etcd's embed does); `/members` reads the cluster; `/members/promote` forwards to a
promote nobody requests (no client of the deployment calls `MemberPromote`); `/members/hashkv` and
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
