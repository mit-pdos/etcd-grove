/-
**The EPaxos kit, closed** (dsverify-lab's epaxos-net kit on examples/lib/remote; notes/dsv-epaxos.md):
seventeen machines, none of which crashes -- the orchestrator (`remote.Check` of ten clients'
operations against the key-value store with pending writes, porcupine over kit.go's `Model()`),
ten client machines (each `remote.ServeClient`, an operation a `Propose` to a replica over TCP,
`Op`) and six servers (server 1 the master, `master.Run`, net/rpc over HTTP on the wildcard
`":7501"`; servers 2..6 the EPaxos replicas of swiftpaxos, each registering with the master, then
`epaxos.New` and its net/rpc service over HTTP) -- deployed at `epAddrs` (`DistDeploy`: the
addresses distinct and valid, no connection, no listener). In every execution of fewer than `remoteStepBound` (`2 ^ 63`) steps along which every machine keeps fewer than `rpcThreadBound` (`2 ^ 30`) live threads, no thread of any
machine is stuck and none has a top-level panic (`Robust`, `Robustness/Statement.lean`). Since
the orchestrator panics unless porcupine accepts the history, this says porcupine accepts every
history, under every fault the net extension allows.

The bounds: `2 ^ 63` steps (remote's clock, `receiptBound ≤ 2 ^ 63`) and fewer than `2 ^ 30` live
threads per machine: Net's net/rpc server (`Server.ServeCodec.spec`, run under net/http's `Serve` by
the master and the replicas) needs the machine's thread bound `threadBound GF ≤ 2 ^ 31` (its wait
group's counter is an `int32`), and net/http's first initialization (Net's `net.http.wp_init_first`)
`threadBound GF ≤ 2 ^ 30` (the reader-slot pools of `DefaultServeMux`'s `RWMutex`), which the
deployment bridge (`Bridge.lean`, `robust_of_distProtoLisRBTT`, over Perennial's
`goose_dist_adequacy_below`) takes along the execution at hand, `Robust`'s `threads`.

gods' treemap, which `state` keeps its store in, is not a premise: its specs are proved of gods'
own code (`github_com.emirpasic.gods.maps.treemap.hyps_true`, notes/gods-verified.md).

**Premises**: none beyond the deployment. net/rpc and net/http (the client over HTTP, the server,
`DefaultServeMux`, the packages' first initializations on the server machines) are `Net/`'s proved
specs, over the interim trust-boundary axioms listed in `etc/tcb-collections/dsv-epaxos.txt`
(net/http's first-run initializer, its `Handle` and `Serve`, net/rpc's and net/http's
`wp_initialize'`); the server machines' own packages' first initializations are proved
(`BootLinked.lean`, `BootCmdsLinked.lean`).
Proved in `Dsverify/Proof/github_com/imdea_software/swiftpaxos_epaxos/examples/epaxosnet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.Bounds
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.TopLevelDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Treemap
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def epaxos_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [client4_sem : cmd.client4.Assumptions]
    [client5_sem : cmd.client5.Assumptions]
    [client6_sem : cmd.client6.Assumptions]
    [client7_sem : cmd.client7.Assumptions]
    [client8_sem : cmd.client8.Assumptions]
    [client9_sem : cmd.client9.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [server6_sem : cmd.server6.Assumptions]
     [go.BasicIntoValInj],
    ∀ (σ : Nat → state) (g : GlobalState),
    DistDeploy epAddrs (system σ) g →
    Robustness.Robust [] (system σ) g rpcThreadBound remoteStepBound

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
