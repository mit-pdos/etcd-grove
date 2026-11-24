-- written by etc/premcheck.py --variant from Dsverify/Spec/rabia/examples/rabianet/TopLevelRobustness.lean
/-
**The rabia kit, closed** (dsverify-lab's rabia-r1wake-1 on examples/lib/remote; notes/dsv-rabia.md):
twelve machines, none of which crashes -- the orchestrator (chooses a configuration at random and
sends it to every client machine and to the servers it names, then `remote.Check` of six clients'
eight operations against the key-value map with pending puts), six client machines (each waits for
the configuration, configures Rabia and connects its Rabia client endpoint, then
`remote.ServeClient`) and five server machines (each waits for the configuration and, if it is one
of its `n` servers, runs a Rabia server; rabia over TCP) -- deployed at `rabiaKitAddrs`
(`DistDeploy`: the addresses distinct and valid, no connection, no listener). In every execution
of fewer than `2^63` steps, with any number of threads, no thread of any machine is stuck and none
has a top-level panic (`Robust`, `Robustness/Statement.lean`). Since the orchestrator panics unless
porcupine accepts the history, this says porcupine accepts every history, under every fault the
net extension allows.

**The challenge's premise**: `KitLibs` (the agent's class, `PremCheckTest.rabiabad.KitLibs`), at every
machine's heap: what the system's libraries do, as `etc/premcheck.py` admits it (each field a
Hoare triple about a library function or method, a library package's `InitHyp`, or library
data; never the system's code, the kit's protocol or this conclusion), with a non-vacuity
instance of `kitLibs.premise`. The landed kit's own premises are one solution.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.TopLevelDefs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import PremCheckTest.rabiabad.KitLibs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace rabia.examples.rabianet

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
    [client4_sem : cmd.client4.Assumptions]
    [client5_sem : cmd.client5.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    ∀ G L, letI := heapAt G L; KitLibs remoteGF

/-- See the file header. -/
def rabia_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [client4_sem : cmd.client4.Assumptions]
    [client5_sem : cmd.client5.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; KitLibs remoteGF) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy rabiaKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)

end rabia.examples.rabianet
end Perennial
