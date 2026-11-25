/-
**The craq kit, closed** (dsverify-lab's craq-bump-1 on examples/lib/remote; notes/dsv-craq.md):
twelve machines, none of which crashes -- the orchestrator (chooses a configuration at random,
sends it to the client and chain machines, then `remote.Check` of five clients' operations
against the key-value map with pending puts, porcupine over kit.go's `Model()`), five client
machines (each waits for the configuration, registers the codec, then `remote.ServeClient`; a put
is the coordinator's `Write`, a get a chain node's `Read`), the coordinator's machine and five
chain machines (go-craq's `coordinator` and `node` over net/rpc over HTTP) -- deployed at
`craqKitAddrs` (`DistDeploy`). In every execution of fewer than `remoteStepBound` (`2 ^ 63`) steps along which every
machine keeps fewer than `rpcThreadBound` (`2 ^ 30`) live threads, no thread of any machine is stuck and none has a
top-level panic (`Robust`). Since the orchestrator panics unless porcupine accepts the history,
this says porcupine accepts every history, under every fault the net extension allows.

**The bounds**: `2 ^ 63` steps (remote's clock, `receiptBound ≤ 2 ^ 63`) and fewer than `2 ^ 30`
live threads per machine: net/rpc's server (Net's `Server.ServeHTTP.spec`/`ServeCodec.spec`, run
under `HandleHTTP`'s handler by the coordinator's and the chain machines) needs the machine's
thread bound `threadBound ≤ 2 ^ 31` (its `sync.WaitGroup`'s counter is an `int32`), and net/http's
first initialization (Net's `net.http.wp_init_first`) `threadBound ≤ 2 ^ 30` (the reader-slot pools
of `DefaultServeMux`'s `RWMutex`), which the deployment bridge (dsv-epaxos's
`robust_of_distProtoLisRBT`, here with no wildcard listener, over Perennial's
`goose_dist_adequacy_below`) takes along the execution at hand, `Robust`'s `threads`.

**Premises** (each at the bundle `remoteGF`, for every machine's heap `heapAt G L` and the start's
`NetProtoGS`):
* `LogHyp`: `log.Default` and `*Logger`'s `Printf`/`Println` on the operands craq logs (`argOk`),
  which Perennial's trusted `log` model leaves without a body (its axiom review refuted it as
  axioms: `fmt` calls an operand's `Format`/`GoString`, `notes/axiom-review/dsv-fix4/log-logger.md`);
* `RpcHttpServe` (`Craq/HttpRpc.lean`): `http.ListenAndServe(a, nil)` serves `a`'s connections with
  `DefaultServeMux`, over Net's `muxRpc` and models-rpc-http's `RpcWorld` and `rpcAddrP` (Net proves
  `http.Serve` on a listener, not `ListenAndServe`).
Not premises: net/rpc's server side but `ListenAndServe` (`rpc.HandleHTTP`, `rpc.RegisterName` of a
fresh name), net/rpc's client over HTTP (`rpc.DialHTTP`), each machine's boot (the codec registry,
net/rpc's and net/http's package variables) and the allocation of the net/rpc world at the server
addresses are proved, over `Net/`'s specs. The trust-boundary axioms the proof rests on are listed
in `etc/tcb-collections/dsv-craq.txt`.
Proved in `Dsverify/Proof/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.Bounds
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.TopLevelDefs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.HttpRpc
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.despreston.go_craq.examples.craqnet

open github_com.despreston.go_craq
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (rabia's). -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

/-- See the file header. -/
def craq_remote_robust.spec : Prop :=
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
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; LogHyp remoteGF) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, RpcHttpServe remoteGF) →
    ∀ (σ : Nat → state) (g : GlobalState),
    DistDeploy craqKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g rpcThreadBound remoteStepBound

end github_com.despreston.go_craq.examples.craqnet
end Perennial
