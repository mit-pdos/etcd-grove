/-
**The SwiftPaxos kit, closed** (dsverify-lab's swiftpaxos kit, run swift-n2nofast-1, on
examples/lib/remote; notes/dsv-swiftpaxos.md): thirteen machines, none of which crashes -- the
orchestrator (the configuration and leader-change protocol, then `remote.Check` of six clients'
operations against the key-value store with pending writes, porcupine over kit.go's `Model()`),
six client machines (each `remote.ServeClient`, an operation a SwiftPaxos client's `Write`/`Read`)
and six servers (server 1 the master, `master.Run`, net/rpc over HTTP on the wildcard `":7001"`;
servers 2..6 the SwiftPaxos replicas, each registering with the master, then `swift.New`) --
deployed at `swAddrs` (`DistDeploy`: the addresses distinct and valid, no connection, no
listener). In every execution of fewer than `2 ^ 31 - 1` steps, with any number of threads, no
thread of any machine is stuck and none has a top-level panic (`Robust`). Since the orchestrator
panics unless porcupine accepts the history, this says porcupine accepts every history, under
every fault the net extension allows.

**The step bound** is `2 ^ 31 - 1`, not `2 ^ 63` (remote's clock, `receiptBound ≤ 2 ^ 63`, would
allow more): Net's net/rpc server (`Server.ServeCodec.spec`, run by the master and the replicas)
needs the machine's thread bound `threadBound ≤ 2 ^ 31` (its `sync.WaitGroup`'s counter is an
`int32`), and the deployment bridge bounds the threads by the step count (`Bridge.lean`,
`robust_of_distProtoLisRBT_sha`). A full real run (the orchestrator's 15 s and 30 s waits, the
clients' and replicas' polling loops, thirteen processes) may take more GooseLang steps than that,
so the theorem covers every prefix of fewer than `2 ^ 31 - 1` steps of such a run, not the whole of
a long one.

**The start message narrows the deployment**: the kit's orchestrator sends each client node its
start (the configuration again, on the node's start port, `conf.startP`) only after every node has
acknowledged its configuration (every predicted replica registered with the master), and a client
node connects (`swift.NewClient`) only after its start. So clients connect only once every node is
configured; a deployment whose clients connect earlier is not covered.

gods' treemap, which `state` keeps its store in, is not a premise: its specs are proved of gods'
own code (`github_com.emirpasic.gods.maps.treemap.hyps_true`, notes/gods-verified.md).

**Premises** (visible; each at the kit's bundle `netDistGF`, for every machine's heap `heapAt G L`
and the start's net protocol names `π`):
* `l`, the libraries' representation choice (`SwiftNetPkgState`/`SwiftLibs`, `Base.lean`): gob's
  encoder/decoder predicates and gob's wire format (`GobFmt`, the field `gobFmt`), each argued true
  of the real library in its docstring;
* the package initializers without a proof here (`InitHyp`, `etc/dsv/README.md`): math/rand's,
  net/rpc's, net/http's, encoding/json's, encoding/gob's, os/signal's, google/uuid's;
* the library specs (`SwiftHyps`, `Hyps.lean`: gob, bufio's lab lemmas, uuid's `ID`;
  `math.rand.Hyps`, dsv-rabia's `math/rand` specs), the environment (`os.signal.NoSignals usr1Sigs`,
  dsv-rabia's class at SIGUSR1: no SIGUSR1 is sent; `SwiftOsRandom`: the OS's randomness does not
  fail, uuid's `New`);
* net/rpc over HTTP (`lib/RpcHttpHyps.lean`; Net's `models-rpc-http`, not landed, named after its
  shapes): the addresses' and listeners' protocols (`RpcHttpAddr`, per global ghost state) and the
  specs (`RpcHttpHyp`, per heap);
* net/rpc's first initialization on a machine (`RpcFirstInit`, `lib/RpcBoot.lean`): it returns
  net/rpc's boot resources (`rpcBootRes`). The kit's own packages' first initializations are
  proved (`BootLinked.lean`, `BootCmdsLinked.lean`).
Proved in `Dsverify/Proof/github_com/imdea_software/swiftpaxos/examples/swiftnet/TopLevelRobustness.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.TopLevelDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcBoot
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Dsverify.Proof.encoding.json.Init
public import Dsverify.Proof.encoding.gob.Init
public import Dsverify.Proof.os.signal.Init
public import Dsverify.Proof.github_com.google.uuid.Init
public import Dsverify.Proof.math.rand.Init
public import Dsverify.Proof.math.rand.Spec
public import Dsverify.Proof.os.signal.Spec

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net Dsv

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open github_com.imdea_software.swiftpaxos

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has

/-- See the file header. -/
def swiftpaxos_remote_robust.spec : Prop :=
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
    [server6_sem : cmd.server6.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (l : SwiftNetPkgState netDistGF),
    (∀ G L, letI := heapAt G L; math.rand.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; net.rpc.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; net.http.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; encoding.json.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; encoding.gob.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; os.signal.InitHyp netDistGF) →
    (∀ G L, letI := heapAt G L; github_com.google.uuid.InitHyp netDistGF) →
    (∀ G L (π : NetProtoGS), letI := heapAt G L; letI := libsAt l π; SwiftHyps netDistGF) →
    (∀ G L, letI := heapAt G L; math.rand.Hyps netDistGF) →
    (∀ G L, letI := heapAt G L; os.signal.NoSignals usr1Sigs netDistGF) →
    (∀ G L (π : NetProtoGS), letI := heapAt G L; letI := libsAt l π; SwiftOsRandom netDistGF) →
    ∀ (ra : ∀ (G : GooseGlobalGS HasLC.hasLC netDistGF) (π : NetProtoGS), letI := G;
        letI := libsAt l π; RpcHttpAddr netDistGF)
      (rh : ∀ G L (π : NetProtoGS), letI := heapAt G L; letI := libsAt l π; letI := ra G π; RpcHttpHyp netDistGF),
    (∀ G L (π : NetProtoGS), letI := heapAt G L; letI := libsAt l π; letI := ra G π; letI := rh G L π;
      RpcFirstInit (GF := netDistGF)) →
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy swAddrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 31 - 1)

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
