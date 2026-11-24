/-
The EPaxos kit's deployment (notes/dsv-epaxos.md): its seventeen machines' boot programs, its
addresses (`Start.lean`'s `epAddrs`), the machines' heaps (`heapAt`) and the server machines' boot
resources (`rpcBootRes`, `RpcBoot`): the definitions its top-level statement
(`Spec/github_com/imdea_software/swiftpaxos_epaxos/examples/epaxosnet/TopLevelRobustness.lean`) names
(as craq's and paxos's `TopLevelDefs.lean`).
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.orch.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client0.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client7.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client8.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.client9.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.cmd.server6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Start
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

section system
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the seventeen machines, from the local states `σ i`: the orchestrator, client
machines 0..9, server machines 1..6 (server 1 the master, 2..6 the replicas; each a command of
`examples/epaxosnet/cmd`). -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0),
   (boot cmd.client0.initialize' cmd.client0.main, σ 1),
   (boot cmd.client1.initialize' cmd.client1.main, σ 2),
   (boot cmd.client2.initialize' cmd.client2.main, σ 3),
   (boot cmd.client3.initialize' cmd.client3.main, σ 4),
   (boot cmd.client4.initialize' cmd.client4.main, σ 5),
   (boot cmd.client5.initialize' cmd.client5.main, σ 6),
   (boot cmd.client6.initialize' cmd.client6.main, σ 7),
   (boot cmd.client7.initialize' cmd.client7.main, σ 8),
   (boot cmd.client8.initialize' cmd.client8.main, σ 9),
   (boot cmd.client9.initialize' cmd.client9.main, σ 10),
   (boot cmd.server1.initialize' cmd.server1.main, σ 11),
   (boot cmd.server2.initialize' cmd.server2.main, σ 12),
   (boot cmd.server3.initialize' cmd.server3.main, σ 13),
   (boot cmd.server4.initialize' cmd.server4.main, σ 14),
   (boot cmd.server5.initialize' cmd.server5.main, σ 15),
   (boot cmd.server6.initialize' cmd.server6.main, σ 16)]

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the proof makes, one
per machine): the global ghost state `G` and the local `L`, its local context `lctx` (rabia's). -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

end system

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [log.Assumptions] [net.http.Assumptions]

/-- A server machine's boot resources, made by its program's initialization (dsv-craq's F2): net/rpc's
codec state before the program's `Register()` (`codecFresh`), net/rpc's package variables as its
server and clients read them (`srvEnv`: `io`'s and `sync`'s facts, `io.EOF`, `ErrUnexpectedEOF`,
`ErrDeadlineExceeded`, net/rpc's `errFrame`, `ErrShutdown`, `debugLog`, `invalidRequest`; this
part's net/rpc package fact is `True` (`Dsverify/Proof/net/rpc/Init.lean`), so they come with the
boot, where craq's came with the fact), `DefaultServeMux` with nothing registered
(`muxOwner []`, net/http's; `RpcHttpHyp`), net/rpc's `DefaultServer` (`∃ γs, defaultServer γs`:
what the initializer's `DefaultServer = NewServer()` makes) and what `DialHTTP` reads (`dialEnv`:
models-rpc-http's `httpEnv`, `bufio`'s, `io`'s, `fmt`'s and `strconv`'s initialization and
net/http's `NoBody`, and net/rpc's `connected`, `"200 Connected to Go RPC"`; net/http's package
fact is `True` here too). -/
def rpcBootRes [RpcHttpAddr GF] [RpcHttpHyp GF] : IProp GF :=
  iprop(codecFresh ∗ net.rpc.srvEnv ∗ RpcHttpHyp.muxOwner [] ∗
    (∃ γs, RpcHttpHyp.defaultServer γs) ∗ dialEnv)

/-- **A server machine's boot premise** (dsv-craq's `RpcBoot`): command `pkg`'s initializer `init`,
run once from the machine's empty package state (only the deployment's boot holds `ownGoState ∅`,
once per machine), initializes the program (any package table `getIs` consistent with `pkg`'s) and
returns the machine's boot resources `rpcBootRes`. -/
def RpcBoot [RpcHttpAddr GF] [RpcHttpHyp GF] (init : val) (pkg : GoString)
    [IsPkgInit (IProp GF) pkg] [GetIsPkgInitWf (IProp GF) pkg] : Prop :=
  ∀ getIs : GoString → IProp GF, GetIsPkgInitProp pkg getIs →
  {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
    (App (Val init) (Val #()))
  {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg ∗ rpcBootRes }}

end boot

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
