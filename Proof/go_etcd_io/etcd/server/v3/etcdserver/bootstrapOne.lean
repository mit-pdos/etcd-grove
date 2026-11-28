/-
**The interim bootstrap axiom** (2026-11-24; `notes/decisions.md`, "The interim bootstrap axiom at one
member"): `bootstrap(cfg)`'s spec at a one-member initial cluster of one peer URL
(`Spec/.../etcdserver/bootstrapOne.lean`), the one form of `bootstrap`'s contract the one-member
examples' closed theorems use (`etcdstart.premises`). **Interim: retired when #34 proves `bootstrap`**
(`bootstrap.wp_proof` linked with no hypothesis left, `etc/link-lean-first-server.txt`'s
`etcdserver_bootstrap`), as `bootstrap.specOne_of_spec` of that result (`BootOneDefs.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **Interim trust boundary: `bootstrap(cfg)` at a one-member initial cluster of one peer URL**
(`bootstrap.specOne`; interim, retired when #34 proves `bootstrap`). Until 2026-11-24 its content was
the closed theorems' Iris premise `etcdstart.premises` (`bootstrapContract` at every such
configuration); it is `bootstrap.spec` (#34's, reviewed with `bootOk`, `notes/bootstrap-proof-plan.md`)
at the one-member configurations.

Why it is true of Go (`server/etcdserver/bootstrap.go:54-156` at the etcd pin `30df685e4`): at a first start
(`NewCluster`, the WAL area fresh, `wal.Exist` false) `bootstrap` touches the data and member
directories (`fileutil.TouchDirAll`, `:65`, `:69`), makes the snapshot directory and the snapshotter
(`bootstrapSnapshot`, `:240-283`), opens the backend in the free backend file and creates its meta bucket
(`bootstrapBackend`), builds the cluster from the initial map (`bootstrapNewClusterNoWAL`:
`VerifyBootstrap`, `NewClusterFromURLsMap`, `isMemberBootstrapped`, which with no other member sends no
request and answers `false`), creates the WAL in its fresh area (`bootstrapNewWAL`, `wal.Create`), finalizes
the cluster (`SetID`, `SetBackend`) and builds raft's start (`bootstrapRaftFromCluster`: one conf change
per member, `json.Marshal(cl.Member(id))` as its context, `raftConfig`). Each step either returns an
error (`bootstrap` then closes what it opened and returns it) or leaves what `bootOk` names, at Go's id
(`computeMemberID`), contexts and directory (`bootGo`, `BootValues.lean`); #34's stage proofs
(`bootstrap.wp_proof` over its callees, `Proof/.../etcdserver/bootstrap*.lean`) check this down to the
callees still open: `advertiseMatchesCluster`, `isMemberBootstrapped`, `MemberIDs`/`MemberByName`/`Member`
under `clusterMem`, `zap.Logger.Named`, the WAL metadata's marshal, `wal.Create` in the fresh area, the
cluster rows (`bootClusterRows`), the file-system laws, `bootstrapBackend`'s two laws, and
`bootstrapSnapshot`'s link. The restriction to one member of one URL is what makes it true of Go where
the unrestricted spec is not (the spec file's header). -/
axiom bootstrap.wp_proofOne : bootstrap.specOne (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
