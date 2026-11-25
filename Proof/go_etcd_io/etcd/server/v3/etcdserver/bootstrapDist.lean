/-
**The interim bootstrap axiom at `etcd_safe`'s deployment shape** (2026-11-25; `notes/etcd-dist-plan.md` §16.3):
`bootstrap(cfg)`'s spec at a first start of a member whose initial cluster has up to 64 entries of one peer URL
each, the other members' peer URLs on other machines (`Spec/.../etcdserver/bootstrapDist.lean`). It replaces the
Iris premise `bootstrapContract` (inside `etcdstart.bootPremise`) on `etcd_safe`'s line: the member boots derive
the contract from it (`etcd_dist.bootPremiseDist_of_specDist`, `dist/BootDist.lean`). **Interim: retired when #34
proves `bootstrap` at these clusters** (its restated spec, with the round tripper's contract), as
`bootstrap.specDist_of_spec` of that result. Go evidence: `examples/axiomcx/bootstrapdist`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **Interim trust boundary: `bootstrap(cfg)` at a first start of a member of `etcd_safe`'s deployment**
(`bootstrap.specDist`; interim, retired when #34 proves `bootstrap` at these clusters). It is `bootstrap.spec`
(#34's, reviewed with `bootOk`) at the clusters of up to 64 members of one peer URL each, with the round
tripper's contract `etcd_dist.bootRTOk` for the requests to the other members.

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
return an error (`member %s has already been bootstrapped`); the answer is from etcd's peer handler of a member
of the same cluster (`httpPeerSvc`'s acceptor protocol), whose `/members` is a JSON list of members. Then
`bootstrapNewWAL` creates the WAL, `Finalize` sets the cluster's id and backend, and `bootstrapRaftFromCluster`
builds raft's start (one conf change per member, `json.Marshal(cl.Member(id))` as its context). Each step
either returns an error (`bootstrap` closing what it opened) or leaves what `bootOk` names at Go's id, contexts
and directory (`bootGo`), as #34's stage proofs check down to the callees still open (`bootstrap.wp_proof`).
The Go test `examples/axiomcx/bootstrapdist` boots three members of this shape through `NewServer` (success),
and one whose peers are unreachable (`isMemberBootstrapped` answers `false`, the boot succeeds) and one whose
data directory is a file (an error returned, no panic). -/
axiom bootstrap.wp_proof_dist [π : Net.NetProtoGS] : bootstrap.specDist (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
