/- Lean-first (no Rocq counterpart).
# `raft/kvnet`: the top-level robustness theorem, stated (2026-11-22)

`raft_kvnet_robust`: kvnet (`examples/raft/kvnet`: kvdurable's replicated key-value store on raft, every
replica a process of its own talking to its peers and clients over TCP, its durable state in files)
as an instance of the generic robustness statement (`Robustness/Statement.lean`, `Robust crashing
stable g threads bound`); `raft_kvnet_robust_example`, its instance at one deployment. This file only
states them (the file to audit); the definitions they name are in
`KvNet/Proof/.../kvnet/TopLevelDefs.lean`, the proofs in `KvNet/Proof/.../kvnet/TopLevelRobustness.lean`.
The statement was agreed with the user on 2026-11-20 (`notes/kvnet-robust-goal.md`); adapted here to
`Robust`'s thread bound (none: `threads := bound + 1`, as kvdurable's) and to the decided bound on
`MaxInflightMsgs` (`< 2^62`, raft's `RestartNode`'s; Go's `ValidCluster` checks it).

**What it says.** Replica `i + 1` runs `kvnetReplicaProgram` (kvnet's initialization, then
`RunNode(i + 1, addrs, dir, <raft's options>)`) on a machine of its own that may crash at any step
and restart (with its program), listening at the `i`-th address of `addrs`; one client machine
that never crashes runs `kvcheckProgram` (kvcheck's initialization, then `Check(addrs, voters)`).
`Check` is the test's driver: 4 clients of 100 random Put/Get/Read operations through random
replicas (retried until answered), configuration changes and leadership disruptions, its history
traced with a counter clock and checked by porcupine with no timeout; it **panics unless porcupine
answers `Ok`**. So "no thread of any machine has a top-level panic" includes: the client's history
is linearizable against kvnet's model. Both programs also panic on a configuration the premises
exclude (so the theorem's coverage is decided by the premises, not by Go code).

**The premises.** Raft's options valid for the number of replicas (`ClusterConfig.Ok`); fewer than
`2^32` replicas; distinct addresses, each canonical `a.b.c.d:p` (`Net.addrOk`: IPv4 unicast, port
nonzero and below the ephemeral range); on every replica's machine, `dir` a root of its file system
with nothing in it. `Robust` itself requires every machine to be a fresh Go process (one context
`lctx`) and the machines and the network to start in their extensions' initial states (no
listener, no connection; the files as on disk).

**The extensions are fixed**: the net extension and the Linux file extension (`kvnetExts`), and
nothing else. Their trusted semantics assume an environment, stated here in prose:
- the file extension's (`GooseLang/Ext/Fs/Impl.lean`, its header): one replica per file system,
  nothing else touches its tree, and a killed process's file system is synced before it restarts
  (configuration C: Linux 7.0, ext4 with its defaults, `notes/axiom-review/fs-config/`);
- the net extension's closed world: no process outside the deployment listens at or dials the
  replicas' addresses.

**Trusted beyond Lean's axioms and these extensions' semantics**: the Goose translations of the
programs and of the packages they reach (kvnet, kvcheck, raft-noax's raft, `durable`, porcupine,
lintest, gokv's `trusted_proph`, the standard library's models), the trusted `net` model, and the
package-assumption instances the statement takes (`kvcheck.Assumptions`, which includes those of
every package kvcheck imports, kvnet's among them; `net.FieldAssumptions`).

Safety only: an operation no replica ever answers keeps `Check` running (no deadline), which the
theorem allows.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open NetFs

section statement
attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExts_hasNet kvnetExts_hasFs
variable [go_gctx : GoGlobalContext]

/-- **kvnet is robust** (see the file header). Replica `i + 1` listens at `replicas[i].1` and runs on
the machine `replicas[i].2`; the client runs on the machine `σc`. -/
def raft_kvnet_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions],
  ∀ (cl : ClusterConfig) (dir : GoString) (replicas : List (GoString × state)) (σc : state)
    (g : GlobalState),
    cl.Ok replicas.length →
    replicas.length < 2 ^ 32 →
    (replicas.map (·.1)).Nodup →
    (∀ a σ, (a, σ) ∈ replicas →
      Net.addrOk a = true ∧                               -- canonical a.b.c.d:p
      dir ∈ (fsOf σ).fs.roots.map (·.1) ∧                 -- dir is an empty root
      ∀ c, (fsOf σ).lookup (joinPath dir [c]) = none) →
    let addrs := List.intercalate go!"," (replicas.map (·.1))
    Robustness.Robust
      (replicas.mapIdx fun i p => (kvnetReplicaProgram cl addrs dir (W64 ((i : Int) + 1)), p.2))
      [(kvcheckProgram cl addrs, σc)]
      g (threads := 2 ^ 61 + 1) (bound := 2 ^ 61)

/-- The example deployment's options: 5 replicas, 3 of them bootstrap voters (the driver adds the
others). -/
def exampleConfig : ClusterConfig :=
  { voters := 3, preVote := true, checkQuorum := true, stepDownOnRemoval := true,
    maxSizePerMsg := 1048576, maxCommittedSizePerReady := 1048576, maxInflightMsgs := 256 }

/-- **kvnet is robust, an example**: replicas 1..5 at 10.0.0.1:7001 .. 10.0.0.5:7001, durable state
in /var/lib/kvnet. A corollary of `raft_kvnet_robust`. -/
def raft_kvnet_robust_example.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
    [field_sem : net.FieldAssumptions],
  ∀ (σ₁ σ₂ σ₃ σ₄ σ₅ σc : state) (g : GlobalState),
    (∀ σ ∈ [σ₁, σ₂, σ₃, σ₄, σ₅],
      go!"/var/lib/kvnet" ∈ (fsOf σ).fs.roots.map (·.1) ∧
      ∀ c, (fsOf σ).lookup (joinPath go!"/var/lib/kvnet" [c]) = none) →
    let addrs := go!"10.0.0.1:7001,10.0.0.2:7001,10.0.0.3:7001,10.0.0.4:7001,10.0.0.5:7001"
    let dir := go!"/var/lib/kvnet"
    Robustness.Robust
      [(kvnetReplicaProgram exampleConfig addrs dir 1, σ₁),
       (kvnetReplicaProgram exampleConfig addrs dir 2, σ₂),
       (kvnetReplicaProgram exampleConfig addrs dir 3, σ₃),
       (kvnetReplicaProgram exampleConfig addrs dir 4, σ₄),
       (kvnetReplicaProgram exampleConfig addrs dir 5, σ₅)]
      [(kvcheckProgram exampleConfig addrs, σc)]
      g (threads := 2 ^ 61 + 1) (bound := 2 ^ 61)

end statement

end raft_kvnet
end EtcdGrove
end Perennial
