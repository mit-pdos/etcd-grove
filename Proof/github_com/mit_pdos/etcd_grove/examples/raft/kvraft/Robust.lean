/-
Lean-first (no Rocq counterpart).

# kvraft's robustness statement (2026-11-15; redone 2026-11-17; no proof yet)

`examples/raft/kvraft` (`notes/kvraft.md`): kvdurable's replicated key-value store on raft, every
replica a process of its own, talking to its peers and its clients over TCP, its durable state one
file. `kvraftRobust` is what a proof would establish, an instance of the generic statement
(`Robustness/Statement.lean`, `Robust`: machines that crash and restart, machines that never
crash, no top-level panic):

**For every deployment** of replica processes, each running `replica cfg` (its node configuration
`cfg`: id, directory, every replica's address, the cluster's options) on a machine of its own
**that may crash at any step and restart**, with an empty directory of its own and no listener;
and of **one client machine that never crashes**, running `client addrs` (the replicas'
addresses) on another host, with no listener; each a fresh Go process (`Robust`'s premise); on a
fresh network (no connection), every replica address valid (`Net.addrOk`; v3.4 of the net
extension has no plan and no hosts); **in every execution** (Perennial's `DistCrashNsteps`: any interleaving,
any crash of any replica at any step -- a power loss, or a kill followed by a sync, the file
extension's "Restarts" -- and every network fault the TCP semantics allows: bytes delayed,
directions cut, dials failing, which is what partitions and resets are) of fewer than `2^61`
steps, **no thread of any machine is stuck or has a top-level panic**.

The statement mentions no linearizability, no history and no bytes on the network: what the
store guarantees is what the client program checks. The client to prove it for runs the clients'
traffic (`Put`, `Get`, `Read`, configuration changes, disruptions), records its history and
panics unless porcupine accepts it against kvraft's model (as `Main` of kv, kvdurable and
kvwitness does in one process); its machine does not crash, so it keeps its history across the
replicas' crashes.

**The parameters a proof will fix.**
* `replica`: the Goose translation of a replica's process, kvraft's package initialization then
  `RunNode(cfg)` with `cfg`'s Go value; `client`: the translation of the checking client's
  process. Neither is translated yet, and the client does not exist as a program of its own
  (`examples/raft/kvraft/driver` runs the clients together with the harness that kills processes
  and partitions the network, which is the semantics' part here). `kvraftRobust (fun cfg => ...)
  (fun addrs => ...)` is the theorem to prove.
* The extensions: any list of them with the net extension (`[HasExt Net.netExt]`,
  `GooseLang/Ext/Net/Impl.lean`) and the Linux file extension (`[HasExt Fs.fsExt]`: the replicas'
  file, written through `durable.Write`, reimplemented over `os` per `notes/decisions.md`, "One
  file semantics, fsExt; power loss only"), each with its own semantics (`HasExt.sem_eq`).
-/
module

public import Robustness.Statement
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.Net.Deploy
public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Robustness

/-! ## The deployment -/

/-- The cluster's options (kvraft's `Options`). -/
structure Options where
  voters : Nat
  preVote : Bool
  checkQuorum : Bool
  stepDownOnRemoval : Bool
  maxSizePerMsg : Nat
  maxCommittedSizePerReady : Nat
  maxInflightMsgs : Nat

/-- A replica's configuration (kvraft's `NodeConfig`): its id, the directory of its file, every
replica's address by id (its own included), the options. -/
structure NodeConfig where
  id : Nat
  dir : GoString
  addrs : List (Nat × GoString)
  opts : Options

/-- The options raft accepts (`raft.Config.validate`: a positive `MaxInflightMsgs`; not both size
limits `0`, which `newRaft` refuses) and kvraft's (`1 ≤ voters`), within Go's integers. -/
def OptionsOk (o : Options) : Prop :=
  1 ≤ o.voters ∧ o.voters < 2 ^ 64 ∧ ¬ (o.maxSizePerMsg = 0 ∧ o.maxCommittedSizePerReady = 0) ∧
  o.maxSizePerMsg < 2 ^ 64 ∧ o.maxCommittedSizePerReady < 2 ^ 64 ∧
  0 < o.maxInflightMsgs ∧ o.maxInflightMsgs < 2 ^ 63

/-- The replicas' configurations agree on the addresses and options; their ids are distinct, each
nonzero, below `2^64`, with an address; no id or address is listed twice. -/
def ClusterOk (cfgs : List NodeConfig) : Prop :=
  (∀ c ∈ cfgs, ∀ c' ∈ cfgs, c.addrs = c'.addrs ∧ c.opts = c'.opts) ∧
  (cfgs.map NodeConfig.id).Nodup ∧
  (∀ c ∈ cfgs, 1 ≤ c.id ∧ c.id < 2 ^ 64 ∧ ∃ a, (c.id, a) ∈ c.addrs) ∧
  (∀ c ∈ cfgs, (c.addrs.map Prod.fst).Nodup ∧ (c.addrs.map Prod.snd).Nodup ∧
    (∀ p ∈ c.addrs, 1 ≤ p.1 ∧ p.1 < 2 ^ 64) ∧ OptionsOk c.opts)

/-- Every replica's address (from any configuration: they agree). -/
def replicaAddrs (cfgs : List NodeConfig) : List GoString :=
  cfgs.flatMap fun c => c.addrs.map Prod.snd

section deployment
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt Fs.fsExt]
  [HasExt Net.netExt]

/-- The network at the start: no connection. -/
def FreshNet (g : GlobalState) : Prop := (extGlobal Net.netExt g.globalWorld).conns = ∅

/-- The machine with the local state `σ` has no listener. -/
abbrev NoListener (σ : state) : Prop := (extLocal Net.netExt σ.world).lis = ∅

/-- A replica's machine at the deployment's start (a fresh Go process: `Robust`'s premise): no
listener; its files as on disk, its directory one of the file system's roots and empty; and every
replica address valid (`Net.addrOk`, D20). -/
def ReplicaStart (cfg : NodeConfig) (σ : state) : Prop :=
  NoListener σ ∧
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  (∃ j, (cfg.dir, j) ∈ (extLocal Fs.fsExt σ.world).fs.roots) ∧
  (∀ c, (extLocal Fs.fsExt σ.world).lookup (joinPath cfg.dir [c]) = none) ∧
  (∀ p ∈ cfg.addrs, Net.addrOk p.2 = true)

/-- The client's machine at the deployment's start (a fresh Go process: `Robust`'s premise): no
listener. -/
def ClientStart (σ : state) : Prop := NoListener σ

/-- **kvraft's robustness statement** (see the file header), for the replicas' program `replica`
and the client's program `client`: every deployment of replicas configured by `cfgs`, on machines
`sys` that may crash and restart, with the client on a machine `σc` that never crashes, on a
fresh network, is `Robust`: in every execution of fewer than `2^61` steps no
thread of any machine is stuck or has an unrecovered panic. -/
def kvraftRobust [lctx : GoLocalContext] [go.Semantics] (replica : NodeConfig → Expr)
    (client : List GoString → Expr) : Prop :=
  ∀ (cfgs : List NodeConfig) (sys : List state) (σc : state)
    (g : GlobalState),
    ClusterOk cfgs → cfgs.length = sys.length →
    (∀ p ∈ cfgs.zip sys, ReplicaStart p.1 p.2) →
    ClientStart σc →
    FreshNet g →
    Robust ((cfgs.zip sys).map (fun p => (replica p.1, p.2)))
      [(client (replicaAddrs cfgs), σc)] g (threads := 2 ^ 61 + 1) (bound := 2 ^ 61)

end deployment

end kvraft
end EtcdGrove
end Perennial
