-- written by etc/kitlibs-check.py --variant from Dsverify/Spec/github_com/xiang90/paxos/examples/paxosnet/TopLevelRobustness.lean
/-
**The paxos kit, closed** (dsverify-lab's paxos-net-3 on examples/lib/remote; notes/dsv-paxos.md):
ten machines, none of which crashes -- the orchestrator (`remote.Check` of four clients' proposals
against the write-once register with pending proposals), four client machines (each
`remote.ServeClient`, its operation the client's proposal over its own paxos node) and five servers
(three acceptors, two learners; xiang90/paxos over TCP) -- deployed at `paxosKitAddrs` (`DistDeploy`:
the addresses distinct and valid, no connection, no listener). In every execution of fewer than
`2^63` steps, with any number of threads, no thread of any machine is stuck and none has a
top-level panic (`Robust`, `Robustness/Statement.lean`). Since the orchestrator panics unless
porcupine accepts the history, this says porcupine accepts every history, under every fault the
net extension allows. Proved in `Dsverify/Proof/.../paxosnet/TopLevelRobustness.lean`.

**The challenge's premise**: `KitLibs` (the agent's class, `KitLibsCheckTest.paxos.KitLibs`), at every
machine's heap: what the system's libraries do, as `etc/kitlibs-check.py` admits it (each field a
Hoare triple about a library function or method, a library package's `InitHyp`, or library
data; never the system's code, the kit's protocol or this conclusion), with a non-vacuity
instance of `kitLibs.premise`. The landed kit's own premises are one solution.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.TopLevelDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import KitLibsCheckTest.paxos.KitLibs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.xiang90.paxos.examples.paxosnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the
proof makes, one per machine): the global ghost state `G` and the local `L`, its local context
`lctx`. The premise holds of every such heap. -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

/-- The libraries' premise: `KitLibs` at every machine's heap (the non-vacuity instance's type). -/
def kitLibs.premise : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [go.BasicIntoValInj],
    ∀ G L, letI := heapAt G L; KitLibs remoteGF

/-- See the file header. -/
def paxos_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; KitLibs remoteGF) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy paxosKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
