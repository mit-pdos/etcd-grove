/-
# `raft/kvraft`: the definitions its top-level statement is written in (2026-11-22)

The programs kvraft's top-level theorem is about and the other definitions its statement names
(`notes/kvraft-robust-goal.md`, the agreed statement), here so that the statement
(`KvRaft/Spec/.../kvraft/TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers"). Only
scalars and strings cross into the programs: the replicas' addresses as one comma-separated string
(split in Go), the directory, raft's options as `w64`/`Bool`.

* `ClusterConfig`: raft's options for the cluster; `ClusterConfig.Ok cl n`: the options raft and
  kvraft accept for `n` replicas (`raft.Config.validate`; `newRaft` refuses both size limits 0;
  `MaxInflightMsgs` below raft's `RestartNode`'s `2^62`): what Go's `kvraft.ValidCluster` checks
  beyond the addresses (`validCluster`).
* `kvraftReplicaProgram cl addrs dir id`: replica `id`'s process, kvraft's package initialization, then
  `RunNode`.
* `kvcheckProgram cl addrs`: the checking client's process, kvcheck's package initialization, then
  `Check` (which panics unless porcupine, with no timeout, answers `Ok`).
* `fsOf σ`: a machine's Linux file system (the file extension's local state).
-/
module

public import GooseLang.Ext.NetFs.Adequacy
public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open NetFs

/-- Raft's options for the cluster (see the file header). -/
structure ClusterConfig where
  /-- the bootstrap configuration: replicas `1 … voters` -/
  voters : w64
  preVote : Bool
  checkQuorum : Bool
  stepDownOnRemoval : Bool
  maxSizePerMsg : w64
  maxCommittedSizePerReady : w64
  maxInflightMsgs : w64

/-- Options raft and kvraft accept, for a cluster of `n` replicas (see the file header). -/
def ClusterConfig.Ok (cl : ClusterConfig) (n : Nat) : Prop :=
  1 ≤ cl.voters.toNat ∧ cl.voters.toNat ≤ n ∧
  ¬ (cl.maxSizePerMsg = 0 ∧ cl.maxCommittedSizePerReady = 0) ∧
  0 < cl.maxInflightMsgs.toNat ∧ cl.maxInflightMsgs.toNat < 2 ^ 62

section programs
attribute [local instance] kvraftExts
variable [go_gctx : GoGlobalContext]

/-- Replica `id`'s process: kvraft's package initialization, then `RunNode`; `addrs` the replicas'
addresses joined by commas (replica `i` at the `i`-th), `dir` the directory of its durable state. -/
def kvraftReplicaProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs dir : GoString)
    (id : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvraft.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RunNode) #id #addrs #dir #cl.voters
    #cl.preVote #cl.checkQuorum #cl.stepDownOnRemoval #cl.maxSizePerMsg
    #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

/-- The checking client's process: its package initialization, then `Check`. The driver: it runs
the clients' Put/Get/Read operations (retrying across replicas, fresh operation ids and read
sequence numbers), configuration changes and leadership disruptions, records the history with a
counter clock, and panics unless porcupine (no timeout) answers `Ok`. A reply that does not
decode counts as no answer. -/
def kvcheckProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Check) #addrs #cl.voters

end programs

section fs
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExts_hasFs

/-- A machine's Linux file system: the file extension's local state. -/
abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

end fs

end kvraft
end EtcdGrove
end Perennial
