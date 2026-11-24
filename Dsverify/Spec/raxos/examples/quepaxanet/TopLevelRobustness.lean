/-
**The QuePaxa kit, closed** (dsverify-lab's quepaxa-bump-1 on examples/lib/remote;
notes/dsv-quepaxa.md): twelve machines, none of which crashes -- the orchestrator (`remote.Check`
of six clients' operations against the key-value map with pending puts), six client machines (each
makes its QuePaxa client, which connects to the five replicas' proxies, then `remote.ServeClient`)
and five server machines (each a QuePaxa replica: its proxy, its recorder served over gRPC, its
proposers; QuePaxa over TCP) -- deployed at `quepaxaKitAddrs` (`DistDeploy`: the listed addresses
distinct and valid, no connection, no listener; the servers' wildcard listeners `0.0.0.0:port` are
the proof's business, dsv-epaxos's
`epaxosnet/Bridge.lean`). In every execution of fewer than `2^63` steps, with
any number of threads, no thread of any machine is stuck and none has a top-level panic (`Robust`,
`Robustness/Statement.lean`). Since the orchestrator panics unless porcupine accepts the history,
this says porcupine accepts every history, under every fault the net extension allows.

**Premises** (visible; each a hypothesis class of the proof at the bundle `remoteGF`, for every
machine's heap `heapAt G L`, or for the global ghost state `G`; notes/dsv-quepaxa.md, "Hypotheses"):
* the initializers of the libraries with no translation or model here (`InitHyp`: yaml.v2, go-redis
  v8, io/ioutil, encoding/gob, grpc, grpc/codes, math/rand: each runs without panicking);
* `qv : hyp.QpVocab remoteGF`, the abstract vocabulary of the gRPC and `sync.Map` hypotheses (any:
  the premises below are about it);
* protobuf's `Marshal`/`Unmarshal` of QuePaxa's messages (`hyp.PbHyp`), math/rand's `Seed` and
  package-level `Intn` (`hyp.RandHyp`), `time.Time.UTC` (`hyp.UtcHyp`), `sort.Ints`
  (`hyp.SortHyp`), `fmt.Println` (`hyp.PrintlnHyp`), gRPC's unary path over `qv.grpc` and the codec
  `hyp.qpCodec` (`hyp.grpc.GrpcHyp`, for every heap and every protocol registry `NetProtoGS`), a gRPC
  world's registry can be allocated (`hyp.grpc.GrpcWorldHyp`, over the global ghost state), and
  `sync.Map` over `qv.map` (`hyp.sync.MapHyp`);
* the translation's `Assumptions` of the twelve commands (with, by their instances, those of every
  package they import), `net.FieldAssumptions` and `go.BasicIntoValInj`, as paxos's statement.
Proved in `Dsverify/Proof/raxos/examples/quepaxanet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.TopLevelDefs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared
public import Dsverify.Proof.raxos.Hyp
public import Dsverify.Proof.gopkg_in.yaml_v2.Init
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.io.ioutil.Init
public import Dsverify.Proof.encoding.gob.Init
public import Dsverify.Proof.google_golang_org.grpc.Init
public import Dsverify.Proof.google_golang_org.grpc.codes.Init
public import Dsverify.Proof.math.rand.Init

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace raxos.examples.quepaxanet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the
proof makes, one per machine): the global ghost state `G` and the local `L`, its local context
`lctx`. The heap premises below hold of every such heap. -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

/-- See the file header. -/
def quepaxa_remote_robust.spec : Prop :=
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
    [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; gopkg_in.yaml_v2.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; github_com.go_redis.redis.v8.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; io.ioutil.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; encoding.gob.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; google_golang_org.grpc.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; google_golang_org.grpc.codes.InitHyp remoteGF) →
    (∀ G L, letI := heapAt G L; math.rand.InitHyp remoteGF) →
    ∀ (qv : raxos.hyp.QpVocab remoteGF),
    (∀ G L, letI := heapAt G L; raxos.hyp.PbHyp remoteGF) →
    (∀ G L, letI := heapAt G L; raxos.hyp.RandHyp remoteGF) →
    (∀ G L, letI := heapAt G L; raxos.hyp.UtcHyp remoteGF) →
    (∀ G L, letI := heapAt G L; raxos.hyp.SortHyp remoteGF) →
    (∀ G L, letI := heapAt G L; raxos.hyp.PrintlnHyp remoteGF) →
    (∀ G L (π : NetProtoGS), letI := heapAt G L;
      raxos.hyp.grpc.GrpcHyp (cd := raxos.hyp.qpCodec) qv.grpc) →
    (∀ G : GooseGlobalGS HasLC.hasLC remoteGF, raxos.hyp.grpc.GrpcWorldHyp (Gg := G) qv.grpc) →
    (∀ G L, letI := heapAt G L; raxos.hyp.sync.MapHyp qv.map) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy quepaxaKitAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)

end raxos.examples.quepaxanet
end Perennial
