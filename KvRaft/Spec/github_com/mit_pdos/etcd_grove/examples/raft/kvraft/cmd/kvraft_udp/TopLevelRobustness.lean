/- Lean-first (no Rocq counterpart).
# `raft/kvraft/cmd/kvraft-udp`: the top-level robustness theorem, stated (2026-11-24, draft)

`kvraft_udp_robust`: kvraft-udp (kvraft's replicated key-value store with the replicas' raft messages over
UDP datagrams, `kvraft.RunNodeUDP`; the clients' requests still over TCP) as an instance of the generic
robustness statement (`Robustness/Statement.lean`). **Exactly kvraft's statement**
(`KvRaft/Spec/.../kvraft/TopLevelRobustness.lean`, agreed 2026-11-20: `notes/kvraft-robust-goal.md`), its
premises and vocabulary reused unchanged (`kvraft.ClusterConfig`), with three
differences: replica `i + 1` runs `kvraftUdpReplicaProgram` (`RunNodeUDP` for `RunNode`), the
extensions are `[netExt, fsExt, udpExt]` (`NetFsUdp.kvraftUdpExts`), and the thread bound is named
(below). The definitions are in
`KvRaft/Proof/.../kvraft/cmd/kvraft_udp/TopLevelDefs.lean`, the proof in
`KvRaft/Proof/.../kvraft/cmd/kvraft_udp/TopLevelRobustness.lean`.

**What it says.** As kvraft's: replica `i + 1` runs on a machine of its own that may crash at any step
and restart, listening (TCP) and bound (UDP) at the `i`-th address of `addrs`; the client machine never
crashes and runs `Check`, which panics unless porcupine answers `Ok`. The UDP network may lose,
duplicate, reorder and delay any datagram, and deliver garbage for one longer than `Udp.intactMax`
bytes (the UDP extension's semantics, `GooseLang/Ext/Udp/Impl.lean`, U1-U13); kvraft-udp sends none.

**The configuration is checked by the programs, not by premises** (2026-11-24, as kvraft's). Both
programs return at once, doing nothing, on a configuration they cannot run: `Check` unless the
addresses (`addrs` split at its commas) are distinct, each canonical `a.b.c.d:p` (IPv4 unicast, port
nonzero and below the ephemeral range), fewer than `2^32`, with the bootstrap voters among them (Go's
`kvraft.ValidAddrs`); `RunNodeUDP` unless, besides, raft's options are valid (`kvraft.ValidCluster`:
`ClusterConfig.Ok`), its id is one of the replicas, and `dir` is shorter than `2^39` bytes: the same
checks as `RunNode`'s, in the same order. So the theorem covers every configuration, and its coverage
of the real runs is the Go checks' (`examples/raft/kvraft`'s `validate_test.go`, `RunNodeUDP`'s path
included). Every address the UDP endpoint uses is then canonical (`Net.addrOk`, which the UDP
extension's `ValidDest` uses), so `openUDP`'s check of its own address cannot fail.

**The premises** are kvraft's, verbatim. The UDP extension adds none: `Robust` requires its initial
state (`Udp.UdpGlobal.init`: no datagram sent; a fresh machine has no socket). `dir` holds both of a
replica's files (its storage, `replica-<id>`, and its boot counter, `udp-boot-<id>`); empty at the
start.

**The extensions are fixed**: kvraft's two and the UDP extension. Their trusted semantics assume an
environment, stated here in prose: kvraft's (one replica per file system, nothing else touches its tree,
a killed process's file system synced before it restarts; no process outside the deployment listens at
or dials the replicas' addresses), and the UDP extension's closed world: no process outside the
deployment sends datagrams to the replicas' addresses.

**Trusted beyond kvraft's**: the UDP extension's semantics, the trusted models of `net.ListenUDP`,
`(*UDPConn).WriteToUDP` and `(*UDPConn).ReadFromUDP` (`Net/TrustedCode/net.lean`, section "UDP"), and
the package assumption `net.UdpFieldAssumptions` (the layout of `UDPConn`/`UDPAddr` those models read).

**The bounds**:
* Steps: fewer than `2 ^ 61`, the most the proof allows: raft's cluster invariant needs `receiptBound + bootLen ≤ 2 ^ 61` (`readyFits_intro`).
* Threads: fewer than `kvraftUdpThreads = 2 ^ 61 + 1` per machine, which excludes nothing: a machine starts with one thread and each step forks at most one.

Safety only, as kvraft's.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.cmd.kvraft_udp.TopLevelDefs
public import KvRaft.ManualProof.net
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelRobustness
public import Robustness.Statement
public import Proof.log.NewModel

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace kvraft_udp

open NetFsUdp kvraft

section statement
attribute [local instance] kvraftUdpExts kvraftUdpExtsSemantics kvraftUdpExts_hasNet kvraftUdpExts_hasFs
  kvraftUdpExts_hasUdp
variable [go_gctx : GoGlobalContext]

/-- **kvraft-udp is robust** (see the file header). Replica `i + 1` listens and is bound at
`replicas[i].1` and runs on the machine `replicas[i].2`; the client runs on the machine `σc`. -/
def kvraft_udp_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
    [udp_field_sem : net.UdpFieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (cl : ClusterConfig) (dir : GoString) (replicas : List (GoString × state)) (σc : state)
    (g : GlobalState),
    (∀ a σ, (a, σ) ∈ replicas →
      dir ∈ (fsOf σ).fs.roots.map (·.1) ∧                 -- dir is an empty root
      ∀ c, (fsOf σ).lookup (joinPath dir [c]) = none) →
    let addrs := List.intercalate go!"," (replicas.map (·.1))
    Robustness.Robust
      (replicas.mapIdx fun i p => (kvraftUdpReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      [(kvraftUdpCheckProgram cl addrs, σc)]
      g (threads := kvraftUdpThreads) (bound := 2 ^ 61)

/-- **kvraft-udp is robust, an example**: kvraft's example deployment (`kvraft.exampleConfig`), with
UDP. A corollary of `kvraft_udp_robust`. -/
def kvraft_udp_robust_example.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
    [udp_field_sem : net.UdpFieldAssumptions]
    [log_sem : log.NewModel],
  ∀ (σ₁ σ₂ σ₃ σ₄ σ₅ σc : state) (g : GlobalState),
    (∀ σ ∈ [σ₁, σ₂, σ₃, σ₄, σ₅],
      go!"/var/lib/kvraft" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup (joinPath go!"/var/lib/kvraft" [c]) = none) →
    let addrs := go!"10.0.0.1:7001,10.0.0.2:7001,10.0.0.3:7001,10.0.0.4:7001,10.0.0.5:7001"
    let dir := go!"/var/lib/kvraft"
    Robustness.Robust
      [(kvraftUdpReplicaProgram exampleConfig addrs dir 1, σ₁),
       (kvraftUdpReplicaProgram exampleConfig addrs dir 2, σ₂),
       (kvraftUdpReplicaProgram exampleConfig addrs dir 3, σ₃),
       (kvraftUdpReplicaProgram exampleConfig addrs dir 4, σ₄),
       (kvraftUdpReplicaProgram exampleConfig addrs dir 5, σ₅)]
      [(kvraftUdpCheckProgram exampleConfig addrs, σc)]
      g (threads := kvraftUdpThreads) (bound := 2 ^ 61)

end statement

end kvraft_udp
end EtcdGrove
end Perennial
