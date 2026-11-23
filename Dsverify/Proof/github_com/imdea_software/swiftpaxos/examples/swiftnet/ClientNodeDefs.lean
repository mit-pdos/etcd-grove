/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeDefs.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md), for the kit over remote.

Client node `c`'s predicates and the specs of its pieces (kit.go's `Sys`, `newClient`, `op`,
`connect`, `changeLeaders`, `clientNode`, `Client`):

* `nodeEnv γ`: what the node's operations and leader changes need of the run (persistent): the
  master's and the replicas' rpc addresses over HTTP (`rpcHttp`) and services, the codec, the
  replicas' ports' protocols, `sp.inv`;
* `isSysL γ c s`: `s` is the node's `*Sys`: its read-only fields hold the addresses and the
  configuration (with `conf.is γ cf`), its mutex `mu` guards `done`, its mutex `opMu` guards the
  operation count `ops` (at most `MaxOps`) and the client `b` (`clSt`), the node's claimed ghost
  (`client.nodeGhostOk γ.sp (cl c)`, from `awaitConf`'s first acknowledgment) and every predicted
  node's registration (`sp.allPredsReg`, from the start message: what the client's connect needs);
* `clSt γ s c j`: `s.b` before operation `j`: nil, with the protocol's sequence number 0 of the
  client id `c + 1` unused, or a connected client ready at sequence number `sq ≤ j` (a failed
  connect uses an operation index but no sequence number, so `sq` lags behind `j`);
* `codecFresh`: net/rpc's codec state before the program's `Register()` (a boot resource of the
  machine, dsv-craq's finding F2; as dsv-epaxos's).

Everything is under the node's `HeapGS`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewClientLog
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewBufferClient
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Connect
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Disconnect
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Write
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Read
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.NewClient
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.CodecG
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientLin
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.Codec
public import Net.Spec.net.rpc.SetCodec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.imdea_software.swiftpaxos.examples.swiftnet

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace cnode

/-- Client `c`'s SwiftPaxos client id (`int32(c) + 1`). -/
def cidOf (c : Nat) : w32 := W32 ((c + 1 : Nat) : Int)

/-- The predicted node of client id `cidOf c` is client node `c`. -/
theorem cidOf_pnode (c : Nat) (hc : c < 6) : (cidOf c).toNat - 1 = c := by
  unfold cidOf
  have : ((c + 1 : Nat) : Int) < 2 ^ 32 := by omega
  simp only [BitVec.toNat_ofInt]
  omega

/-- `MaxOps`: the most operations a client node makes. -/
def maxOps : Nat := 1000

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

/-- The Go value of a configuration (`kit.go`'s `Conf`). -/
def confV (c : Conf) : examples.swiftnet.Conf :=
  ⟨W64 c.n, W64 c.fastRead, W64 c.pool, W64 c.desc⟩

/-- The run's persistent facts the node's operations (their connect) and leader changes need. -/
def nodeEnv (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(rpcHttp γ.W masterAddr ∗ ([∗list] a ∈ replicaRpcAddrs, rpcHttp γ.W a) ∗
    ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
    net.rpc.codecSet net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
    ([∗list] a ∈ replicaAddrs, addrProto a (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem)) ∗
    sp.inv γ.sp γ.conf γ.mem γ.lin ∗ globalAddr swift.useFastAckPool ↦□ false)

instance nodeEnv_persistent (γ : SwiftNames netDistGF) : Persistent (nodeEnv γ) := by
  unfold nodeEnv; infer_instance

/-- The node's client (`s.b`) before its operation `j`. -/
def clSt (γ : SwiftNames netDistGF) (s : Loc) (c : Nat) (j : Nat) : IProp netDistGF :=
  iprop((s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗ sp.clientSeq γ.sp (cidOf c) 0) ∨
    ∃ (b : Loc) (sq : Nat), s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null ∧ sq ≤ j⌝ ∗
      client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) sq)

/-- `opMu`'s lock invariant: the operation count (at most `MaxOps`) and the client before it. -/
def opInv (γ : SwiftNames netDistGF) (s : Loc) (c : Nat) : IProp netDistGF :=
  iprop(∃ j : w64, s.[examples.swiftnet.Sys, go!"ops"] ↦ j ∗ ⌜uint.nat j ≤ maxOps⌝ ∗
    clSt γ s c (uint.nat j))

/-- `s` is client node `c`'s `*Sys` (see the file header; persistent). -/
def isSysL (γ : SwiftNames netDistGF) (c : Nat) (s : Loc) : IProp netDistGF :=
  iprop(∃ (cf : Conf) (asl : GoSlice),
    s.[examples.swiftnet.Sys, go!"addrs"] ↦□ asl ∗ asl ↦*□ addrs ∗
    s.[examples.swiftnet.Sys, go!"conf"] ↦□ confV cf ∗ conf.is γ cf ∗
    sync.isMutex (s.[examples.swiftnet.Sys, go!"mu"])
      (∃ d : w64, s.[examples.swiftnet.Sys, go!"done"] ↦ d) ∗
    sync.isMutex (s.[examples.swiftnet.Sys, go!"opMu"]) (opInv γ s c) ∗
    nodeEnv γ ∗ client.nodeGhostOk γ.sp (sp.PNode.cl c) ∗ sp.allPredsReg γ.sp γ.conf)

instance isSysL_persistent (γ : SwiftNames netDistGF) c s : Persistent (isSysL γ c s) := by
  unfold isSysL; infer_instance

/-- The interface value of the node's `*Sys` at `s`. -/
def sysV (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType examples.swiftnet.Sys.ty) #s

theorem clSt_advance (γ : SwiftNames netDistGF) (s : Loc) (c j j' : Nat) (h : j ≤ j') :
    clSt γ s c j ⊢ clSt γ s c j' := by
  unfold clSt
  iintro (H | ⟨%b, %sq, Hb, %Hb, Hr⟩)
  · ileft; iexact H
  · iright
    iexists b, sq
    iframe Hb Hr
    ipureintro; exact ⟨Hb.1, by omega⟩

/-- A dialer machine's net/rpc state (persistent; a boot resource): the receipt bound, the
client's and `DialHTTP`'s package state (`rpcHttp` less the address). -/
def cliBoot : IProp netDistGF :=
  iprop(⌜receiptBound netDistGF ≤ 2 ^ 64⌝ ∗ net.rpc.cliEnv ∗ dialEnv)

instance cliBoot_persistent : Persistent (cliBoot (hG := hG)) := by
  unfold cliBoot; infer_instance

/-- net/rpc's codec state as its initialization leaves it, before the program's `Register()`
(exclusive: a boot resource of the machine). -/
def codecFresh : IProp netDistGF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset)

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]
variable [ρ : RemoteGS]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `Addrs()`: a new slice of the nodes' first addresses. -/
abbrev AddrsC.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.Addrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* addrs }}

/-- `at(addrs, 1+c, ConfOff)`: client node `c`'s configuration port. -/
abbrev atConf.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #(W64 1 + W64 (c : Int))))
      (Val #(W64 2000)))
  {{ RET #(clientConfAddrs.getD c go!""); sl ↦*{dq} addrs }}

/-- `at(addrs, 1+c, StartOff)`: client node `c`'s start port. -/
abbrev atStart.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #(W64 1 + W64 (c : Int))))
      (Val #(W64 3000)))
  {{ RET #(clientStartAddrs.getD c go!""); sl ↦*{dq} addrs }}

/-- `host(addrs[NC+1])`: the master's host. -/
abbrev hostMaster.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.host)) (Val #(go!"127.0.0.1:7001")))
  {{ RET #(go!"127.0.0.1"); True }}

/-- `port(addrs[NC+1])`: the master's port. -/
abbrev portMaster.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.port)) (Val #(go!"127.0.0.1:7001")))
  {{ RET #(W64 7001); True }}

/-- `Register()`: the kit's codec registered. -/
abbrev Register.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ codecFresh }}
    (App (Val (@! examples.swiftnet.Register)) (Val #()))
  {{ RET #(); net.rpc.codecSet net.rpc.RpcCodec.spec }}

/-- `at(addrs, NC+node, RPCOff)`: server node `node`'s rpc port (`node` a replica's server node,
2..6). -/
abbrev atRpc.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (node : w64), 2 ≤ uint.nat node → uint.nat node ≤ 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #(W64 6 + node)))
      (Val #(W64 1000)))
  {{ RET #(replicaRpcAddrs.getD (uint.nat node - 2) go!""); sl ↦*{dq} addrs }}

/-- The `Replica.BeTheLeader` call of a leader change (`master/RunLoop.lean`'s
`master.wp_call_btl`, restated: a callee's spec). -/
abbrev callBtl.spec : Prop :=
  ∀ (c : Loc) (W : net.rpc.RpcWorld netDistGF) (a : GoString) (γc γm : GName) (cc : Conf)
    (pa btl : Loc),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗
        net.rpc.kitCodecOk ∗
        net.rpc.isClient c W a ∗ ⌜W.SS a go!"Replica" = some (withErr (sp.replicaRpcSpec γc γm))⌝ ∗
        confIs γc cc ∗ pa ↦ replica.defs.BeTheLeaderArgs.mk ∗
        btl ↦ replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.BeTheLeader")))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderArgs.ty) #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderReply.ty) #btl)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ l n : w32, btl ↦ replica.defs.BeTheLeaderReply.mk l n ∗
          ⌜sp.btlOk cc.n l n⌝) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `s.changeLeaders(cs)` (the leader changes' goroutine), each change at a replica's server
node: never panics. -/
abbrev Sys.changeLeaders.spec (γ : SwiftNames netDistGF) (c : Nat) : Prop :=
  ∀ (s : Loc) (sl : GoSlice) (cs : List examples.swiftnet.change),
  (∀ ch ∈ cs, 2 ≤ uint.nat ch.Node' ∧ uint.nat ch.Node' ≤ 6) →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ isSysL γ c s ∗ sl ↦*□ cs }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"changeLeaders"))
      (Val #sl))
  {{ RET #(); True }}

/-- `s.connect(c)` (with `opMu` held): the node's client connected (ready at sequence number 0)
or, on `false`, as it was. -/
abbrev Sys.connect.spec (γ : SwiftNames netDistGF) (c : Nat) : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗
      isSysL γ c s ∗ s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗
      sp.clientSeq γ.sp (cidOf c) 0 }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"connect"))
      (Val #(W64 (c : Int))))
  {{ (ok : Bool), RET #ok;
      if ok then ∃ b : Loc, s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null⌝ ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) 0
      else s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗ sp.clientSeq γ.sp (cidOf c) 0 }}

/-- `op(s, c, in)`: client `c`'s operation on its node, with remote's update of the input `i`:
the step's output with the update's `Φ`, or the unknown output. -/
abbrev op.spec (γ : SwiftNames netDistGF) (γk : GName) (c : Nat) : Prop :=
  ∀ (s : Loc) (i : KIn) (Φ : BStr → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ isSysL γ c s ∗
      cnode.linkInv (G := hG.goose_globalGS) γ γk ∗
      slotUpd (Gg := hG.goose_globalGS) (cnode.swRK (G := hG.goose_globalGS) γk) i Φ }}
    (App (App (App (Val (@! examples.swiftnet.op)) (Val #s)) (Val #(W64 (c : Int))))
      (Val #(inVal i)))
  {{ (o : examples.swiftnet.Out), RET #o; ⌜o = Out.mk true []⌝ ∨
      ∃ w : BStr, ⌜o = Out.mk false w.1⌝ ∗ Φ w }}

/-- `newClient(addrs, c)` on client node `c`, from its share and its boot resources (the node's
fresh ghost, net/rpc's fresh codec state and client state): the node's system. -/
abbrev newClient.spec (γ : SwiftNames netDistGF) (c : Nat) : Prop :=
  ∀ (asl : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ asl ↦* addrs ∗ clientNodeShare γ c ∗
      client.ghostFresh ∗ codecFresh ∗ cliBoot ∗ globalAddr swift.useFastAckPool ↦□ false }}
    (App (App (Val (@! examples.swiftnet.newClient)) (Val #asl)) (Val #(W64 (c : Int))))
  {{ (s : Loc), RET #s; isSysL γ c s }}

/-- `ClientAddrs()`: a new slice of the client nodes' request addresses. -/
abbrev ClientAddrs.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.ClientAddrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }}

/-- What client machine `c` starts with: its share, its boot resources (the node's fresh ghost,
net/rpc's fresh codec state and client state), the link invariant, remote's protocols of its
request address and remote's map of inputs. -/
def clientRes (γ : SwiftNames netDistGF) (γk : GName) (c : Nat) : IProp netDistGF :=
  iprop(clientNodeShare γ c ∗ client.ghostFresh ∗ codecFresh ∗ cliBoot ∗
    globalAddr swift.useFastAckPool ↦□ false ∗
    linkInv (G := hG.goose_globalGS) γ γk ∗
    remoteAddr (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk)
      (clientAddrs.getD c go!"") ∗
    mapCtx (Gg := hG.goose_globalGS) (I := KIn))

/-- `clientNode(addrs, caddr, c)`: client machine `c`'s program at its request address; it never
returns. -/
abbrev clientNode.spec (γ : SwiftNames netDistGF) (γk : GName) (c : Nat) : Prop :=
  ∀ (asl : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ asl ↦* addrs ∗ clientRes γ γk c }}
    (App (App (App (Val (@! examples.swiftnet.clientNode)) (Val #asl))
      (Val #(clientAddrs.getD c go!""))) (Val #(W64 (c : Int))))
  {{ RET #(); False }}

/-- `Client(c)`: client machine `c` (`c < NC = 6`); it never returns. -/
abbrev Client.spec : Prop :=
  ∀ (γ : SwiftNames netDistGF) (γk : GName) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ clientRes γ γk c }}
    (App (Val (@! examples.swiftnet.Client)) (Val #(W64 (c : Int))))
  {{ RET #(); False }}

open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory in
/-- `Orch()`: the orchestrator, from the configuration's writer token, the run's facts, remote's
protocols of the client machines' request addresses, the map of inputs and the pending library
over porcupine's model `swS0` of the store `swRK γk`; it returns (porcupine accepts the
history). -/
abbrev Orch.spec [RpcHttpAddr netDistGF] : Prop :=
  ∀ (γ : SwiftNames netDistGF) (γk : GName) (γp : PendNames), receiptBound netDistGF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ conf.writer γ ∗ common γ ∗
      ([∗list] a ∈ clientAddrs,
        remoteAddr (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (swRK (G := hG.goose_globalGS) γk) (swS0 (GF := netDistGF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (swS0 (GF := netDistGF)) γp (swS0 (GF := netDistGF)).M.init ∗
      [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 24 }}
    (App (Val (@! examples.swiftnet.Orch)) (Val #()))
  {{ RET #(); True }}

end specs

section calltime
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- `callTime()`: some duration. -/
theorem wp_callTime :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
      (App (Val (@! examples.swiftnet.callTime)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

end calltime

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
