/-
`bootstrapRaft(cfg, cluster, bwal)` (`bootstrap.go:534-546` at the etcd pin `edc800c6f`, through
`bootstrapRaftFromCluster`, `:548-572`, and `raftConfig`, `:584-596`; names-only, a callee of
`bootstrap`'s proof, `?` in the server's link until stage 4 proves it). Lean-first; claim #34, stage 3
(2026-11-23), `notes/bootstrap-proof-plan.md` §7.3. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`
(`bootRaftBuilt`) and `BootValues.lean` (`bootGo`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrapRaft(cfg, c, w)` for a new cluster with no WAL read**: from the cluster after
`Finalize` (its lock `isRaftCluster`, the apply thread's half of its members map at `bootGo.memMap`,
its id), the initial cluster's facts (`bootGo.membersOk`), the configuration's timing (`bootCfgOk`), a
zap logger, the WAL record `w` as `bootstrapStorage` wrote it (nothing read) and the storage
registry's authority, empty: the raft record `bv` with `bootOk`'s raft rows (`bootRaftBuilt`: the
configuration at this member's id `bootGo.id`, the peers `bootGo.ps` with the contexts `bootGo.ctxs`,
the fresh registered `MemoryStorage`). The records and the members' half are given back.

Why it is true of Go: `!bwal.haveWAL && cfg.NewCluster` (`:538`), so
`bootstrapRaftFromCluster(cfg, cl, cl.MemberIDs(), bwal)`. `MemberIDs()` (`cluster.go:170-179`) is
the members' ids sorted (`bootGo.ps`); `MemberByName(cfg.Name)` (`:155-168`) is this member's (the
names are the initial cluster's keys, distinct, so no panic); each peer is `raft.Peer{ID: id, Context:
json.Marshal(cl.Member(id))}` (`:551-558`; `Member` clones the member, whose JSON is `bootGo.memberJSON`
for valid UTF-8 and plain URLs, stop S1 of the plan: `json.Marshal` never fails on a `Member`);
`bwal.MemoryStorage()` (`:564`) is `raft.NewMemoryStorage()` with nothing applied, set or appended (no
snapshot, hard state or entries), registered as a ghost step (the registry's authority) with its
sized flag; the record (`:565-571`): the logger, the heartbeat `TickMs * time.Millisecond` (wrapping),
`raftConfig(cfg, member.ID, s)`: `ElectionTick` the configuration's (`1 < ElectionTicks`,
`bootCfgOk`), `HeartbeatTick` `1`, the storage, `MaxSizePerMsg` `2 ^ 20`, `MaxInflightMsgs` `512`,
`CheckQuorum`, `PreVote` the configuration's, no trace logger, and the logger
`NewRaftLoggerZap(cfg.Logger.Named("raft"))`, a raft logger over zap (`isLogger`).

(Claim #34 stage 4, 2026-11-25; ledger, "`bootstrapRaft.spec`: an id raft refuses") With this member's id
not one of raft's local targets (`bootGo.idRaftOk`): `bootRaftBuilt`'s `rnStartCfg` holds `ConfigValid`,
which excludes them (raft's `Config.validate` refuses them), and `membersOk` excludes only `0`. -/
abbrev bootstrapRaft.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (c w : Loc)
    (bc : bootstrappedCluster) (bw : bootstrappedWAL) (dq dqw : DFrac),
  cfg.NewCluster' = true → bootCfgOk cfg → bootGo.membersOk cfg U → bootGo.idRaftOk cfg U →
  bootGo.urlsNe U →
  bw.haveWAL' = false → bw.st' = null → bw.ents' = slice.nil → bw.snapshot' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ c ↦{dq} bc ∗ w ↦{dqw} bw ∗
      membership.isRaftCluster bc.cl' ∗
      membership.clusterCid bc.cl' (bootGo.cid U cfg.InitialClusterToken') ∗
      membership.clusterMem bc.cl' (bootGo.memMap U cfg.InitialClusterToken') ∗
      memStorRegAuth (∅ : GMap Loc MemStorNamesRec) }}
    (App (App (App (Val (@! bootstrapRaft)) (Val #cfg)) (Val #c)) (Val #w))
  {{ (r : Loc), RET #r;
      ∃ bv : bootstrappedRaft, r ↦ bv ∗ bootRaftBuilt cfg U bv ∗
        c ↦{dq} bc ∗ w ↦{dqw} bw ∗
        membership.clusterMem bc.cl' (bootGo.memMap U cfg.InitialClusterToken') }}

end spec

end EtcdGrove
end Perennial
