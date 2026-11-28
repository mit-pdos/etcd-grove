/-
**The hraft kit, closed** (hashicorp/raft v1.8.0's verification fork on examples/lib/remote;
notes/dsv-hraft.md): twelve machines, none of which crashes, deployed at `hraftKitAddrs`
(`DistDeploy`: those addresses distinct and valid, no connection, no listener):

* the orchestrator: picks the first configuration's size (3 or 5 voters) at random and sends it to
  the servers; runs an admin goroutine that forever asks a random server for a random membership
  change of a random server (AddVoter, AddNonvoter, DemoteVoter, RemoveServer), a leadership
  transfer (to any server, or to the one raft picks) or a snapshot; then `remote.Check` of five
  clients' operations, a number drawn at random from 1 to `MaxOps` (`2 ^ 20`) each, against the
  register with pending writes (porcupine over `kit.go`'s `Model()`, run to completion);
* five client machines, each `remote.ServeClient`: an operation is a write through the log
  (`Raft.Apply`) or a read through the log, after a `Barrier`, or with `VerifyLeader` after a
  barrier of the server's term, each tried at the servers in turn;
* six server machines, each hashicorp/raft (`NewRaft`, bootstrapped with servers 1..n0 as voters,
  the others empty) over the kit's net/rpc transport (`examples/hraftnet/rpctransport`: heartbeats
  on the fast path, pipelined replication, snapshots sent in the request), in-memory log and
  stable stores and the snapshot store `examples/snapstore`, with a one-register state machine and
  an API service (`examples/hraftnet/service`), all on one net/rpc server.

In every execution of fewer than `hraftStepBound` (`2 ^ 62`) steps along which every machine keeps
fewer than `hraftThreadBound` (`2 ^ 28`) live threads, no thread of any machine is stuck and none
has a top-level panic (`Robust`). Since the orchestrator panics unless porcupine accepts the
history, this says porcupine accepts every history, under every fault the net extension allows
(connections cut at any read or write, any delay); the servers' own panics (raft's, and the state
machine's on a snapshot it did not write) are excluded too.

**The bounds** are the proof's. Steps: raft's terms and indexes stay below `2 ^ 62`, where its
arithmetic on them cannot wrap (`hraftStepBound`; within remote's `2 ^ 63`). Threads: raft's
goroutine helper and its `RWMutex`es split each thread token in four (`hraftThreadBound`; within
net/rpc's server's `2 ^ 31`, its `WaitGroup`'s `int32` counter, and net/http's first
initialization's `2 ^ 30`, which net/rpc imports).

**Premises**: none beyond the deployment. The configuration (the first configuration's size, each
server's raft options) is chosen by the programs and validated in Go (`raft.ValidateConfig`; an
invalid one returns). The classes are the translations' package assumptions (`cmd.*.Assumptions`,
`go.BasicIntoValInj`); the extension is the net extension (`netExts`), closed world (only the
deployment's machines use the network). Trusted besides: the Goose translation of the fork and the
kit (`Dsverify/Code/github_com/hashicorp/`), the net/rpc model and its codec generated from
`examples/hraftnet/rpc.toml` (`models/net/rpc/rpcgen.py`), Net's interim axioms; the axioms the
proof rests on are listed in `etc/tcb-collections/dsv-hraft.txt`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def hraft_nocrash_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [client4_sem : cmd.client4.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [server6_sem : cmd.server6.Assumptions]
    [go.BasicIntoValInj]
    (σ : Nat → state) (g : GlobalState),
    DistDeploy hraftKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g hraftThreadBound hraftStepBound

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
