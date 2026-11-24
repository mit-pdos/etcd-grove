/- Lean-first (no Rocq counterpart).

`etcdserver.NewServer` on a member machine of a distributed deployment: an interim trust-boundary axiom until phase
7 S5 across machines (`notes/etcd-dist-plan.md`, "Interim transport").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` on a member machine** (interim trust boundary; the spec's file header says what changes from
`NewServer.specG`). What it asserts of etcd v3.6's `NewServer` over the net extension: the construction succeeds
or fails as in one process, and the threads it starts (rafthttp's transport: its peers' stream writers and
readers, pipelines and probers, which dial the other members' peer addresses `http://a` of the directory; the
raft node; the lessor), and its own requests to the peers (bootstrap's `isMemberBootstrapped`: `GET /members` at
each peer, an error ending `NewServer` with an error), neither get stuck nor panic, the bytes written on a
connection to a peer address being requests of etcd's peer API from this member (`httpAddrAt a`'s protocols, `httpPeerSvc`, opaque); its post is
`specG`'s, at network names `γn` with the in-process network's payload (`srvNet γ`) and directory.

Why it is true: `NewServer.wp_proofG` proves `specG`'s text over the in-process network, whose HTTP side
(`netHttpOk`: every other member's host registered with raft's protocol, `http.reserve`) is what the transport's
round trips use. Across machines the round trips go to the other members' peer addresses, which the deployment's
start set to `httpPeerSvc` (`http_addr_set`) and on which only the other members' peer handlers accept
(`PeerServe_dist`): what differs is how a message reaches its receiver, the transport's own code being the same.
The proxy: Go's transport (etcd's `transport.NewTimeoutTransport`, `Proxy: http.ProxyFromEnvironment`) would send
every peer request to an HTTP proxy named by `HTTP_PROXY`/`http_proxy` (`HTTPS_PROXY`/`https_proxy` for `https`
URLs), which may answer anything (raft messages that make the member panic, `commitTo` past its last index);
`noProxyEnv` excludes it: the variables are unset or empty for the run (`os.Getenv.specEnv`), so
`ProxyFromEnvironment` proxies no request.

A connection the transport makes reaches a listener at `a` that may be another program's (`httpAddrAt`'s
`addrProto` lets its holder listen at `a`): such a program can write nothing there (no proof establishes the opaque
acceptor protocol of any bytes), so the transport sees a peer that never answers, which it handles (a timeout, an
error, a retry). Every member's raft ghost state is the cluster's (`nodeBoot γ.cl`, `srvRaftLogInv`, the claims),
allocated once by the start; the network names `γn` the post gives are this member's.

Retired by phase 7 S5 (net/http's client half over the net extension, rafthttp's transport proved across machines)
with `NewServer.wp_proofG` restated over S5's address facts. -/
axiom NewServer_dist.wp_proof [π : NetProtoGS] (on cmp : Bool) :
    NewServer.specG_dist (GF := GF) (hG := hG) on cmp

end proof

end etcd_dist
end EtcdGrove
end Perennial

end
