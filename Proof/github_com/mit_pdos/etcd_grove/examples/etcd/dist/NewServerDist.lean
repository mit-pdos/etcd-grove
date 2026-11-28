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
connection to a peer address being requests of etcd's peer API from this member (`httpAddrAt γ pid a`'s protocols, `httpPeerSvc`, opaque); its post is
`specG`'s, at network names `γn` with the in-process network's payload (`srvNet γ`) and directory.

Why it is true: `NewServer.wp_proofG` (over the translation at the etcd pin `30df685e4` and the bbolt pin `2f6fcff`,
2026-11-28) proves `specG`'s text over the in-process network, whose HTTP side
(`netHttpOk`: every other member's host registered with raft's protocol, `http.reserve`) is what the transport's
round trips use. Across machines the round trips go to the other members' peer addresses, which the deployment's
start set to `httpPeerSvc` (`http_addr_set`), served by the other members' peer handlers (`PeerServe_dist`; any
holder of `httpAddrAt` may also listen and accept there, but write nothing): what differs is how a message reaches its receiver, the transport's own code being the same.
Across machines the members of one cluster read the address facts at their own records, which agree on `γ.cl` (the
index of `httpAddrAt`) and differ at most in the storage registry `γ.reg`: given `γ.cl`, this precondition fixes the
rest (`vs` by `nodeBoot`'s `BootLogOk vs γ.cl.raft.reBoot`, `boot` by `srvRaftLogInv`'s committed lower bound of
length `γ.cl.bootLen`, `rule` by the premise, `snapLoc` by `srvClusterOk`, the log names by `srvLogInv`'s
`ownCommittedOps γ.cl`, `authOn` by `kvInvM on`, one per cluster), and `srvNet` does not read `reg`: the members are
those of one in-process network (`allocN`'s `γn.N = srvNet γ`), with the cluster's ids, contexts and auth mode.
The proxy: Go's transport (etcd's `transport.NewTimeoutTransport`, `Proxy: http.ProxyFromEnvironment`) would send
every peer request to an HTTP proxy named by `HTTP_PROXY`/`http_proxy` (`HTTPS_PROXY`/`https_proxy` for `https`
URLs), which may answer anything (raft messages that make the member panic, `commitTo` past its last index);
`noProxyEnv` excludes it: the variables are unset or empty for the run (`os.Getenv.specEnv`), so
`ProxyFromEnvironment` proxies no request.

A connection the transport makes reaches a listener at `a` that may be another program's (`httpAddrAt`'s
`addrProto` lets its holder listen at `a`): such a program can write nothing there (no proof establishes the opaque
acceptor protocol of any bytes), so the transport sees a peer that never answers, which it handles (a timeout, an
error, a retry). The peer addresses' protocols name the cluster
and the member (`httpAddrAt γ pid a`: `httpPeerSvc γ.cl pid`, raft's cluster names, allocated once per cluster; not the
member's whole record `γ`, whose storage registry `γ.reg` is the member's own, so that every member of the cluster reads
the same fact of an address: 2026-11-25, `notes/axiom-review/s5-cluster-index.md`), and an address is set once
(`addrUnset` spent by `http_addr_set`), so the
transport of a member of another ghost cluster (a second `srvClusterBoot_alloc` with the same configuration: same ids,
another `γ.cl`) can never meet `Hpeers` at these addresses; a duplicate of a member inside `γ.cl` is excluded by the exclusive
`nodeVacant γ.cl id` and `raftState γ.cl id` (`Hnboot`; `nodeBoot` itself is persistent) (review of 2026-11-24: unindexed, two clusters at one address gave a duplicate member and
raft's `tocommit out of range` panic). The network names `γn` the post gives are this member's.

The member's auth names `γa` and lessor name `γl` are the caller's (F7's P-A1 and F2's P-L1, 2026-11-26; review
`notes/axiom-review/f7-combined.md` §1, SOUND): the construction does not depend on ghost names. The lessor part is
proved in one process (`NewServer.specGAt`, `NewServer.wp_proofGAt`, the same `Hlslot` and `mvccLeases E.γ = γl`).
With auth on, the authorities `NewServer` allocates in one process (`auth.authBoot_alloc`, `tokAlloc`,
`srvTpInv_alloc`) are the caller's instead (`authNamesFreshD γa`); no in-process spec takes them yet.

Retired by phase 7 S5 (net/http's client half over the net extension, rafthttp's transport proved across machines)
with `NewServer.wp_proofGAt` restated over S5's address facts. -/
axiom NewServer_dist.wp_proof [π : NetProtoGS] (on cmp : Bool) :
    NewServer.specG_dist (GF := GF) (hG := hG) on cmp

end proof

end etcd_dist
end EtcdGrove
end Perennial

end
