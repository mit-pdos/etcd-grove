/-
**The craq kit, closed** (dsverify-lab's craq-bump-1 on examples/lib/remote; notes/dsv-craq.md):
twelve machines, none of which crashes -- the orchestrator (chooses a configuration at random,
sends it to the client and chain machines, then `remote.Check` of five clients' operations
against the key-value map with pending puts, porcupine over kit.go's `Model()`), five client
machines (each waits for the configuration, registers the codec, then `remote.ServeClient`; a put
is the coordinator's `Write`, a get a chain node's `Read`), the coordinator's machine and five
chain machines (go-craq's `coordinator` and `node` over net/rpc over HTTP) -- deployed at
`craqKitAddrs` (`DistDeploy`). In every execution of fewer than `2 ^ 63` steps along which every
machine keeps fewer than `2 ^ 31` live threads, no thread of any machine is stuck and none has a
top-level panic (`Robust`). Since the orchestrator panics unless porcupine accepts the history,
this says porcupine accepts every history, under every fault the net extension allows.

**The bounds**: `2 ^ 63` steps (remote's clock, `receiptBound ≤ 2 ^ 63`) and fewer than `2 ^ 31`
live threads per machine: net/rpc's server (Net's `Server.ServeHTTP.spec`/`ServeCodec.spec`, run
under `RpcHttpServe`'s `HandleHTTP`/`ListenAndServe` by the coordinator's and the chain machines)
needs the machine's thread bound `threadBound ≤ 2 ^ 31` (its `sync.WaitGroup`'s counter is an
`int32`), which the deployment bridge (dsv-epaxos's `robust_of_distProtoLisRBT`, here with no
wildcard listener, over Perennial's `goose_dist_adequacy_below`) takes along the execution at
hand, `Robust`'s `threads`. (Until 2026-11-24 the bridge bounded the threads by the step count
plus 2, and the step bound was `2 ^ 31 - 1`.)

**Premises** (visible, each a hypothesis of the proof at the bundle `remoteGF`, for every
machine's heap `heapAt G L` and the start's `NetProtoGS`; never an instance):
* H1: net/rpc's and net/http's initializers (`InitHyp`; Net has no initialization proof);
* H6: `LogHyp` (`log.Default` and `*Logger`'s methods, which Perennial's trusted `log` model
  leaves without a body);
* H2/H3, net/rpc's server over HTTP (`RpcHttpServe`: `rpc.HandleHTTP`, `http.ListenAndServe`
  and `DefaultServeMux`), over models-rpc-http's `RpcWorld` and `rpcAddrP`;
* F2: each machine's boot resources from its initialization (`RpcBoot`: the codec registry,
  net/rpc's and net/http's package variables, `DefaultServeMux` unclaimed, `DefaultServer`, Net's
  `net.rpc.defaultServer`).
Not premises: the package-level `rpc.RegisterName` on `DefaultServer` (Net's
`net.rpc.RegisterName.wp`, rpc-defaultserver); net/rpc's client over HTTP (`rpc.DialHTTP`,
models-rpc-http's `DialHTTP.wp`, over `DialHTTPPath` and net/http's `ReadResponse`) is proved,
and so is the allocation of the net/rpc world at the server addresses (Net's `addrs_set_proto` and
the registry's invariant). F1, RemoveNode's method obligation, is proved (net-rpc-errors'
`callRet` admits a forwarded `errAny` error, `cnewArg_RemoveNode`); F3, the chain nodes' `errOk`,
is proved (Net's `errOk` is over the server's own messages, `srvErrMsg`, which Read's not-found is
not; `nodeSpec_errOk`).
Proved in `Dsverify/Proof/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.TopLevelDefs
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitSpecs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init

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
    (∀ G L, letI := heapAt G L; net.rpc.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; net.http.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; LogHyp remoteGF) →
    ∀ (rs : ∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, RpcHttpServe remoteGF),
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.client0.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client0) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.client1.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client1) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.client2.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client2) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.client3.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client3) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.client4.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client4) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server1.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server2.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server2) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server3.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server3) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server4.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server4) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server5.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5) →
    (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
      RpcBoot (GF := remoteGF) cmd.server6.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6) →
    ∀ (σ : Nat → state) (g : GlobalState),
    DistDeploy craqKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g (2 ^ 31) (2 ^ 63)

end github_com.despreston.go_craq.examples.craqnet
end Perennial
