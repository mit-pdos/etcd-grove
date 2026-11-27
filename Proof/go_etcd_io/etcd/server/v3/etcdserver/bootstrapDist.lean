/-
**The interim bootstrap axiom at `etcd_safe`'s deployment shape** (2026-11-25; `notes/etcd-dist-plan.md` §16.3):
`bootstrap(cfg)`'s spec at a first start of a member whose initial cluster has up to `etcd_dist.typed.maxMembers` (1000)
entries of one peer URL each, the other members' peer URLs on other machines (`Spec/.../etcdserver/bootstrapDist.lean`). It replaces the
Iris premise `bootstrapContract` (inside `etcdstart.bootPremise`) on `etcd_safe`'s line: the member boots derive
the contract from it (`etcd_dist.bootPremiseDist_of_specDist`, `dist/BootDist.lean`). **Interim: retired when #34
proves `bootstrap` at these clusters** (its restated spec, with the round tripper's contract), as
`bootstrap.specDist_of_spec` of that result. Go evidence: `examples/axiomcx/bootstrapdist`.

**Why an axiom and not a theorem.** `bootstrap`'s Go is translated with its body, and #34 proves it over its
callees' specs (`bootstrap.wp_proof`), but at `bootstrap.spec`, which is false at this shape (the ledger, B4:
`isMemberBootstrapped` sends `GET /members` to the other members through the round tripper, a right
`bootstrap.spec`'s precondition does not give, and its callee spec `isMemberBootstrapped.spec` is over the
single-process `http.HttpNet`, not the peer addresses across machines). What a proof is missing: #34's restated
spec (`bootstrap.spec` with the round-tripper contract, of which this statement is the instance at `etcd_safe`'s
shape), and `isMemberBootstrapped`'s GETs proved over S5's cross-machine net/http (the client side of
`httpAddrAt`'s peer protocols), which does not exist yet. A Go model or trusted code would not be smaller: the
code is already translated and its first-start path proved over its callees' specs (`wp_bootstrap`, with
#34's open callee hypotheses, B1), so a model would restate
`bootstrap`'s whole first start (backend, WAL, cluster, raft's start) as new trusted code, where this axiom is
`bootstrap.spec`'s reviewed triple with the four shape premises and the one network right added.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **Interim trust boundary: `bootstrap(cfg)` at a first start of a member of `etcd_safe`'s deployment**
(`bootstrap.specDist`; interim, retired when #34 proves `bootstrap` at these clusters). It is `bootstrap.spec`
(#34's, reviewed with `bootOk`) at the clusters of up to `etcd_dist.typed.maxMembers` (1000) members of one peer URL
each, with the round tripper's contract `etcd_dist.bootRTOk` for the requests to the other members.
**The size bound** (raised from 64 to `etcd_dist.typed.maxMembers` = 1000 on 2026-11-27, Upamanyu's approval, rule 41;
delta review pending in `notes/axiom-review/bootstrap-dist.md`): `bootstrap.spec` itself allows up to `2 ^ 58` entries
(`bootGo.initMapOk`, `BootValues.lean`), and `etcd_dist.bootstrap.specDist_of_spec` (`dist/BootDist.lean`) derives
this statement from it without using the bound; the Go argument below names no bound on the cluster's size.

Why it is true of Go (`server/etcdserver/bootstrap.go:53-160` at the etcd pin `e94f33b50`): at a first start
(`wal.Exist` false in the fresh WAL area) `bootstrap` touches the data and member directories, makes the snapshot
directory and the snapshotter, makes the round tripper (`rafthttp.NewRoundTripper`, peer TLS empty:
`bootCfgOk`'s `tlsEmpty`; an error returned), opens the backend, and builds the cluster
(`bootstrapNewClusterNoWAL`): `VerifyBootstrap` (`advertiseMatchesCluster`: this member's one URL equals its
entry's, so `URLStringsEqual` answers `true` with no DNS, and `Sort` of a one-element slice writes nothing),
`NewClusterFromURLsMap`, then `isMemberBootstrapped`, which sends `GET <url>/members` to each other member's
peer URL (`http://a`, `a` set to etcd's peer protocols, `bootRTOk`; no proxy) through an `http.Client` with the
bootstrap timeout: a dial refused, a timeout, a body that does not parse or a member list without this member
make it answer `false` (the boot goes on), and a list where this member has client URLs makes `bootstrap`
return an error (`member %s has already been bootstrapped`); the answer is from etcd's peer handler of member `pid` of the cluster `γ.cl` (`httpPeerSvc`'s acceptor protocol,
written only by `PeerServe_dist`), whose `/members` is a JSON list of members. The axiom ties `γ` to this
configuration only by pure premises (`γ.vs` its ids), so that member may have been started from another
configuration; the axiom needs only that the answer is etcd's: any etcd member's `/members` is
`cluster.Members()`'s `Clone`s, never `null` (`membership/cluster.go:123-131`; scratch evidence in
`notes/axiom-review/s5-cluster-index.md`: strangers answered by a real three-member cluster boot or get "has
already been bootstrapped", no panic). Then
`bootstrapNewWAL` creates the WAL, `Finalize` sets the cluster's id and backend, and `bootstrapRaftFromCluster`
builds raft's start (one conf change per member, `json.Marshal(cl.Member(id))` as its context). Each step
either returns an error (`bootstrap` closing what it opened) or leaves what `bootOk` names at Go's id, contexts
and directory (`bootGo`), as #34's stage proofs check down to the callees still open (`bootstrap.wp_proof`).
**What the round-tripper contract carries** (the review, `notes/axiom-review/bootstrap-dist.md`): a `/members`
answer that is not etcd's (a list with a `null` element) panics `bootstrap` (a nil `*Member` in
`membership.NewClusterFromMembers`, `membership/cluster.go:101`, via `cluster_util.go:122`;
`nonissues/etcd-bootstrap-members-null-panic.md`). The axiom relies on `bootRTOk` for both routes to such an
answer: at a peer address only `PeerServe_dist`'s etcd peer handler writes (`httpPeerSvc` is opaque; its
`/members` is `cluster.Members()`'s JSON, `etcdhttp/peer.go:112-120`), and no proxy redirects the GET
(`noProxyEnv`; the transport's `Proxy` is `http.ProxyFromEnvironment`, `client/pkg/v3/transport/transport.go:42`).
`addrOk` of each address (inside `httpAddrAt`) makes the dialed address the one named (`canonicalAddr` of a
plain `http://d.d.d.d:p`). The Go test `examples/axiomcx/bootstrapdist` (at the pin) boots three members of this shape through `NewServer`:
the first with its peers unreachable (`isMemberBootstrapped` answers `false`, the boot succeeds), the other two
after a `GET /members` answered by the first's peer handler; one whose peer accepts and never answers (the GET
times out, the boot succeeds); and two errors, returned without a panic: a data directory that is a file, and a
peer listing this member with client URLs (`has already been bootstrapped`); and the two panics `bootRTOk`
excludes (`TestNullMemberAtPeer`: a stand-in at the peer address; `TestProxyNull`: an HTTP proxy). -/
axiom bootstrap.wp_proof_dist [π : Net.NetProtoGS] : bootstrap.specDist (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
