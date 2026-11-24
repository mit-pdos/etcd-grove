/- Lean-first (no Rocq counterpart).
# `raft/kvnet/cmd/kvudp`: the top-level robustness theorem, stated (2026-11-24, draft)

`raft_kvudp_robust`: kvudp (kvnet's replicated key-value store with the replicas' raft messages over
UDP datagrams, `kvnet.RunNodeUDP`; the clients' requests still over TCP) as an instance of the generic
robustness statement (`Robustness/Statement.lean`). **Exactly kvnet's statement**
(`KvNet/Spec/.../kvnet/TopLevelRobustness.lean`, agreed 2026-11-20: `notes/kvnet-robust-goal.md`), its
premises and vocabulary reused unchanged (`raft_kvnet.ClusterConfig`, `ClusterConfig.Ok`), with three
differences: replica `i + 1` runs `kvudpReplicaProgram` (`RunNodeUDP` for `RunNode`), the
extensions are `[netExt, fsExt, udpExt]` (`NetFsUdp.kvudpExts`), and the thread bound is named
(below). The definitions are in
`KvNet/Proof/.../kvnet/cmd/kvudp/TopLevelDefs.lean`, the proof in
`KvNet/Proof/.../kvnet/cmd/kvudp/TopLevelRobustness.lean`.

**What it says.** As kvnet's: replica `i + 1` runs on a machine of its own that may crash at any step
and restart, listening (TCP) and bound (UDP) at the `i`-th address of `addrs`; the client machine never
crashes and runs `Check`, which panics unless porcupine answers `Ok`. The UDP network may lose,
duplicate, reorder and delay any datagram, and deliver garbage for one longer than `Udp.intactMax`
bytes (the UDP extension's semantics, `GooseLang/Ext/Udp/Impl.lean`, U1-U13); kvudp sends none.

**The premises** are kvnet's, verbatim. The UDP extension adds no premise: `Robust` requires its
initial state (`Udp.UdpGlobal.init`: no datagram sent; a fresh machine has no socket), and every
replica's address is already canonical (`Net.addrOk`, which the UDP extension's `ValidDest` uses).
`dir` holds both of a replica's files (its storage, `replica-<id>`, and its boot counter,
`udp-boot-<id>`); empty at the start.

**The extensions are fixed**: kvnet's two and the UDP extension. Their trusted semantics assume an
environment, stated here in prose: kvnet's (one replica per file system, nothing else touches its tree,
a killed process's file system synced before it restarts; no process outside the deployment listens at
or dials the replicas' addresses), and the UDP extension's closed world: no process outside the
deployment sends datagrams to the replicas' addresses.

**Trusted beyond kvnet's**: the UDP extension's semantics, the trusted models of `net.ListenUDP`,
`(*UDPConn).WriteToUDP` and `(*UDPConn).ReadFromUDP` (`Net/TrustedCode/net.lean`, section "UDP"), and
the package assumption `net.UdpFieldAssumptions` (the layout of `UDPConn`/`UDPAddr` those models read).

**The bounds**:
* Steps: fewer than `2 ^ 61`, the most the proof allows: raft's cluster invariant needs `receiptBound + bootLen ≤ 2 ^ 61` (`readyFits_intro`).
* Threads: fewer than `kvudpThreads = 2 ^ 61 + 1` per machine, which excludes nothing: a machine starts with one thread and each step forks at most one.

Safety only, as kvnet's.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.TopLevelDefs
public import KvNet.ManualProof.net
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelRobustness
public import Robustness.Statement
public import Proof.log.NewModel

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

open NetFsUdp raft_kvnet

section statement
attribute [local instance] kvudpExts kvudpExtsSemantics kvudpExts_hasNet kvudpExts_hasFs
  kvudpExts_hasUdp
variable [go_gctx : GoGlobalContext]

/-- **kvudp is robust** (see the file header). Replica `i + 1` listens and is bound at
`replicas[i].1` and runs on the machine `replicas[i].2`; the client runs on the machine `σc`. -/
def raft_kvudp_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions] [udp_field_sem : net.UdpFieldAssumptions]
    [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (cl : ClusterConfig) (dir : GoString) (replicas : List (GoString × state)) (σc : state)
    (g : GlobalState),
    cl.Ok replicas.length →
    replicas.length < 2 ^ 32 →
    dir.length < 2 ^ 39 →
    (replicas.map (·.1)).Nodup →
    (∀ a σ, (a, σ) ∈ replicas →
      Net.addrOk a = true ∧                               -- canonical a.b.c.d:p
      dir ∈ (fsOf σ).fs.roots.map (·.1) ∧                 -- dir is an empty root
      ∀ c, (fsOf σ).lookup (joinPath dir [c]) = none) →
    let addrs := List.intercalate go!"," (replicas.map (·.1))
    Robustness.Robust
      (replicas.mapIdx fun i p => (kvudpReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      [(kvudpCheckProgram cl addrs, σc)]
      g (threads := kvudpThreads) (bound := 2 ^ 61)

/-- **kvudp is robust, an example**: kvnet's example deployment (`raft_kvnet.exampleConfig`), with
UDP. A corollary of `raft_kvudp_robust`. -/
def raft_kvudp_robust_example.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions] [udp_field_sem : net.UdpFieldAssumptions]
    [os_file_sem : os.file.FieldAssumptions] [os_stat_sem : os.fileStat.FieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (σ₁ σ₂ σ₃ σ₄ σ₅ σc : state) (g : GlobalState),
    (∀ σ ∈ [σ₁, σ₂, σ₃, σ₄, σ₅],
      go!"/var/lib/kvnet" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup (joinPath go!"/var/lib/kvnet" [c]) = none) →
    let addrs := go!"10.0.0.1:7001,10.0.0.2:7001,10.0.0.3:7001,10.0.0.4:7001,10.0.0.5:7001"
    let dir := go!"/var/lib/kvnet"
    Robustness.Robust
      [(kvudpReplicaProgram exampleConfig addrs dir 1, σ₁),
       (kvudpReplicaProgram exampleConfig addrs dir 2, σ₂),
       (kvudpReplicaProgram exampleConfig addrs dir 3, σ₃),
       (kvudpReplicaProgram exampleConfig addrs dir 4, σ₄),
       (kvudpReplicaProgram exampleConfig addrs dir 5, σ₅)]
      [(kvudpCheckProgram exampleConfig addrs, σc)]
      g (threads := kvudpThreads) (bound := 2 ^ 61)

end statement

end raft_kvudp
end EtcdGrove
end Perennial
