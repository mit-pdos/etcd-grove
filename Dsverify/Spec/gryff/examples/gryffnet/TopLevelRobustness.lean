/-
**The gryff kit, closed** (dsverify-lab's gryff-bump-1 on examples/lib/remote; notes/dsv-gryff.md):
eleven machines, none of which crashes -- the orchestrator (`remote.Check` of six clients'
operations against the register with compare-and-swap and pending operations), six client machines
(each `remote.ServeClient`, its operations Gryff client requests to its replica in proxy mode), the
master and three Gryff replicas (net/rpc over HTTP for registration, Gryff's wire protocol between
replicas and with clients) -- deployed with the client machines at `gryffKitAddrs` (`DistDeploy`:
those addresses distinct and valid, no connection, no listener; the servers listen at wildcards).
In every execution of fewer than `remoteStepBound` (`2 ^ 63`) steps along which every machine keeps fewer than `rpcThreadBound` (`2 ^ 30`)
live threads, no thread of any machine is stuck and none has a top-level panic (`Robust`). Since the orchestrator panics unless porcupine
accepts the history, this says porcupine accepts every history, under every fault the net
extension allows.

**The bounds:** `2 ^ 63` steps (remote's clock, `receiptBound ≤ 2 ^ 63`) and fewer than `2 ^ 30`
live threads per machine: Net's net/rpc server (`Server.ServeCodec.spec`, run under net/http's
`Serve` by the master and the replicas) needs the machine's thread bound `threadBound GF ≤ 2 ^ 31`
(its `sync.WaitGroup`'s counter is an `int32`), and net/http's first initialization (Net's
`net.http.wp_init_first`) `threadBound GF ≤ 2 ^ 30` (the reader-slot pools of `DefaultServeMux`'s
`RWMutex`), which the deployment bridge (dsv-epaxos's `examples/epaxosnet/Bridge.lean`,
`robust_of_distProtoLisRBTT`, over Perennial's `goose_dist_adequacy_below`) takes along the
execution at hand, `Robust`'s `threads`.

**The deployment** is not narrowed beyond `DistDeploy`: a client's operation that cannot reach its
replica (its dial fails or times out, a read fails) is answered unknown, so no ordering of the
machines' starts is assumed (the clients' start wait, `kit.go`'s `Start(c)`, is for performance
only). A client answers at most `K` = 4 operations, later ones unknown (remote's `Check` calls each client
`K` times, with `K · readTries` = 12 of remote's per-client budget units, `budUnits`), and its
operations run under its `Sys` lock.

**Premises**: none beyond the deployment. The library functions the proof uses without a proof here
are per-function trust-boundary axioms, not premises: `sort.Slice` on `[]int32` with `<`
(`sort.Slice.wp_proofInt32Lt`), `math.Pow` (the main tree's `math.Pow.wp_proof`), `math/rand.Seed`
(`math.rand.Seed.wp_proof`); net/rpc and net/http (the client over HTTP, the server,
`DefaultServeMux`, the packages' initializations) are `Net/`'s proved specs, over the interim
trust-boundary axioms (their first-run initializers, net/http's `Handle` and `Serve`); every axiom
the result rests on is listed in `etc/tcb-collections/dsv-gryff.txt`. `encoding/binary`'s varint
functions are Perennial's.
-/
module

public import Dsverify.Proof.Bounds
public import Dsverify.Proof.gryff.examples.gryffnet.TopLevelDefs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace gryff.examples.gryffnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

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
    ∀ (σ : Nat → state) (g : GlobalState),
    DistDeploy gryffKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g rpcThreadBound remoteStepBound

end gryff.examples.gryffnet
end Perennial
