/-
`bootstrapRaftFromCluster(cfg, cl, ids, bwal)` (`bootstrap.go:548-572` at the etcd pin `edc800c6f`), with
its body since claim #34's stage 4 (2026-11-25): `bootstrapRaft`'s new-cluster branch, at the peers
`cl.MemberIDs()`. Lean-first; `notes/bootstrap-proof-plan.md` §7.4. Its vocabulary:
`Proof/.../etcdserver/BootParts.lean` (`bootRaftBuilt`) and `BootValues.lean` (`bootGo`).
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

/-- **`bootstrapRaftFromCluster(cfg, cl, ids, w)` at a first start**: from the cluster `cl` after
`Finalize` (its lock, the apply thread's half of its members map at `bootGo.memMap`, its id), the peers
`ids` holding `bootGo.ps` (`MemberIDs()`), the initial cluster's facts (`bootGo.membersOk`, this
member's id not one of raft's local targets, `bootGo.idRaftOk`), the configuration's timing
(`bootCfgOk`), a zap logger, the WAL record `w` with nothing read and the storage registry's
authority, empty: the raft record `bv` with `bootOk`'s raft rows (`bootRaftBuilt`). The peers, the
record and the members' half are given back.

Why it is true of Go: `MemberByName(cfg.Name)` (`:549`) is this member's clone (its id `bootGo.id`);
`peers[i] = raft.Peer{ID: ids[i], Context: json.Marshal(cl.Member(ids[i]))}` (`:550-558`;
`json.Marshal` of the member's clone is `bootGo.memberJSON` of its value, the encoding/json model's,
and never fails); the `Info` log (`:559-563`); `bwal.MemoryStorage()` (`:564`) with nothing applied,
registered (the registry's authority); the record (`:565-571`) with `raftConfig(cfg, member.ID, s)`. -/
abbrev bootstrapRaftFromCluster.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (cl : Loc) (ids : GoSlice)
    (w : Loc) (bw : bootstrappedWAL) (dqi dqw : DFrac),
  bootCfgOk cfg → bootGo.membersOk cfg U → bootGo.idRaftOk cfg U → bootGo.urlsNe U →
  bw.st' = null → bw.ents' = slice.nil → bw.snapshot' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ ids ↦*{dqi} bootGo.ps U cfg.InitialClusterToken' ∗ w ↦{dqw} bw ∗
      membership.isRaftCluster cl ∗
      membership.clusterCid cl (bootGo.cid U cfg.InitialClusterToken') ∗
      membership.clusterMem cl (bootGo.memMap U cfg.InitialClusterToken') ∗
      memStorRegAuth (∅ : GMap Loc MemStorNamesRec) }}
    (App (App (App (App (Val (@! bootstrapRaftFromCluster)) (Val #cfg)) (Val #cl)) (Val #ids))
      (Val #w))
  {{ (r : Loc), RET #r;
      ∃ bv : bootstrappedRaft, r ↦ bv ∗ bootRaftBuilt cfg U bv ∗
        ids ↦*{dqi} bootGo.ps U cfg.InitialClusterToken' ∗ w ↦{dqw} bw ∗
        membership.clusterMem cl (bootGo.memMap U cfg.InitialClusterToken') }}

end spec

end EtcdGrove
end Perennial
