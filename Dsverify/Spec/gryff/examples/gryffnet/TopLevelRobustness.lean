/-
**The gryff kit, closed** (dsverify-lab's gryff-bump-1 on examples/lib/remote; notes/dsv-gryff.md):
eleven machines, none of which crashes -- the orchestrator (`remote.Check` of six clients'
operations against the register with compare-and-swap and pending operations), six client machines
(each `remote.ServeClient`, its operations Gryff client requests to its replica in proxy mode), the
master and three Gryff replicas (net/rpc over HTTP for registration, Gryff's wire protocol between
replicas and with clients) -- deployed with the client machines at `gryffKitAddrs` (`DistDeploy`:
those addresses distinct and valid, no connection, no listener; the servers listen at wildcards).
In every execution of fewer than `2 ^ 31 - 1` steps, with any number of threads, no thread of any machine
is stuck and none has a top-level panic (`Robust`). Since the orchestrator panics unless porcupine
accepts the history, this says porcupine accepts every history, under every fault the net
extension allows.

**The step bound** is `2 ^ 31 - 1`, not `2 ^ 63` (remote's clock, `receiptBound ≤ 2 ^ 63`, would
allow more): Net's net/rpc server (`Server.ServeCodec.spec`, run under `RpcHttpHyp`'s `HandleHTTP`/
`Serve` by the master and the replicas) needs the machine's thread bound `threadBound ≤ 2 ^ 31`
(its `sync.WaitGroup`'s counter is an `int32`), and the deployment bridge bounds the threads by
the step count plus 2 (`robust_of_distProtoLisRBT`, dsv-epaxos's `examples/epaxosnet/Bridge.lean`).
A full real run (the clients' start waits, `StartMs` = 4 s plus the stagger, the replicas' and
master's loops, eleven processes) may take more GooseLang steps than that, so the theorem covers
every prefix of fewer than `2 ^ 31 - 1` steps of such a run, not the whole of a long one.

**The deployment** is not narrowed beyond `DistDeploy`: a client's operation that cannot reach its
replica (its dial fails or times out, a read fails) is answered unknown, so no ordering of the
machines' starts is assumed (the clients' start wait, `kit.go`'s `Start(c)`, is for performance
only). What the kit's Go does differently from the lab's (notes/dsv-gryff.md, "Kit Go changes"):
a client answers at most `K` = 4 operations, later ones unknown (remote's `Check` calls each client
`K` times, with `K · readTries` = 12 of remote's per-client budget units, `budUnits`), and its
operations run under its `Sys` lock.

**Premises** (library pieces not proved in the model; each a hypothesis about real Go, never an
instance; notes/dsv-gryff.md, "Hypotheses"): the initializers of the names-only packages
`net/rpc`, `net/http`, `math/rand` (`InitHyp`: they run without panicking; their conditions name
every package the initializers reach, dsv-inithyp-fix); `encoding/binary`'s varint functions
(`BinaryVarintHyps`); `strings.Index` on a one-byte separator (`StringsIndexHyp`); `sort.Slice` on
`[]int32` with `<` (`SortSliceHyp`); `math.Pow` (`MathPowHyp`, the main tree's `math.Pow.spec`);
`math/rand.Seed` (`RandSeedHyp`, the shared `math.rand.Seed.spec`); net/rpc's server over HTTP up
to the hijack (`RpcHttpAddr`, the listeners' protocols, over the global state; `RpcHttpHyp`, the
specs, per heap; Upamanyu's intended shapes); net/rpc's and net/http's owned initializations on a
machine where they have not run yet (`RpcBootHyp`: the codec state, `DefaultServer`, the package
variables their client and server read, the unclaimed `DefaultServeMux`; the table before and
after agree beyond the package, and the `InitHyp` conditions (`GetIsPkgInitProp`) it takes constrain
every package of the initializer's closure, as swiftpaxos's `RpcFirstInit`). Net's net/rpc client
over HTTP (`DialHTTP`, `DialHTTPPath` over net/http's `ReadResponse`) is proved (models-rpc-http),
not a premise. Each holds of every machine heap (`heapAt`) and protocol registry.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.TopLevelDefs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import Dsverify.Proof.net.rpc.Init
public import Dsverify.Proof.net.http.Init
public import Dsverify.Proof.math.rand.Init
public import Dsverify.Proof.gryff.Wire.Proof.VarintWp
public import Dsverify.Proof.gryff.N.StrIndex
public import Dsverify.Proof.gryff.Lib.SortHyps
public import Dsverify.Proof.gryff.Lib.MathHyps
public import Dsverify.Proof.gryff.Lib.RandHyps
public import Dsverify.Proof.gryff.Rpc.RpcHttpHyps

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace gryff.examples.gryffnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (rabia's). -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

/-- See the file header. -/
def gryff_remote_robust.spec : Prop :=
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
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj] [rpc_sem : net.rpc.Assumptions],
    (∀ G L, letI := heapAt G L; net.rpc.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; net.http.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; math.rand.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; wire.BinaryVarintHyps remoteGF) →
    (∀ G L, letI := heapAt G L; netN.StringsIndexHyp remoteGF) →
    (∀ G L, letI := heapAt G L; replica2.SortSliceHyp remoteGF) →
    (∀ G L, letI := heapAt G L; lib.MathPowHyp remoteGF) →
    (∀ G L, letI := heapAt G L; lib.RandSeedHyp remoteGF) →
    ∀ (RA : ∀ (G : GooseGlobalGS HasLC.hasLC remoteGF) (π : NetProtoGS), letI := G;
        RpcHttpAddr remoteGF)
      (H : ∀ G L (π : NetProtoGS), letI := heapAt G L; letI := RA G π; RpcHttpHyp remoteGF),
    (∀ G L (π : NetProtoGS), letI := heapAt G L; letI := RA G π; letI := H G L π;
      RpcBootHyp remoteGF) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy gryffKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 31 - 1)

end gryff.examples.gryffnet
end Perennial
