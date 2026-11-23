/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Client node `c`'s predicates (stage 2: `ClientNodeSpec`'s choices for the adapter's client side,
`kit.go`'s `Sys`, `NewClient`, `Op`):

* `nodeEnv γ`: what the node's operations and leader changes need of the run (persistent): the
  master's and the replicas' rpc addresses and services, the codec, the replicas' ports'
  protocols, `sp.inv`;
* `isSysL γ c s`: `s` is the node's `*Sys`: its read-only fields hold the addresses and the
  configuration (with `conf.is γ cf`), its mutex guards `done`, and the node's claimed ghost
  (`client.nodeGhostOk γ.sp (cl c)`, from `awaitConf`'s first acknowledgment);
* `clSt γ s c j`: `s.b` before operation `j`: nil, with the protocol's sequence number 0 of the
  client id `c + 1` unused, or a connected client ready at sequence number `sq ≤ j` (a failed
  connect uses an operation index but no sequence number, so `sq` lags behind `j`; any `j' ≥ j`
  keeps it, which is `tok_advance`);
* `isSys`/`clientTok`: the same over the `interface{}` value `NewClient` returns.

The rpc codec `C` is a section variable (decision D6, as stage 1's client proofs: the frozen
statements are at `kitCodec`, the link uses `examples.swiftnet.kitCodecC`).

Everything is under the node's `HeapGS` (the token holds the node's points-to's).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.registerRPC
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewClientLog
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewBufferClient
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Connect
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Disconnect
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Write
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Read
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.NewClient
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.CodecG

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

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

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
-- the rpc codec (decision D6, Proof/swiftnet/KitLike.lean): the link uses `kitCodecC`
variable [C : net.rpc.RpcCodec netDistGF]

/-- The Go value of a configuration (`kit.go`'s `Conf`). -/
def confV (c : Conf) : examples.swiftnet.Conf :=
  ⟨W64 c.n, W64 c.fastRead, W64 c.pool, W64 c.desc⟩

instance rpcAddr_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr W a) := by
  unfold net.rpc.rpcAddr; infer_instance

/-- The run's persistent facts the node's operations (their connect) and leader changes need. -/
def nodeEnv (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(net.rpc.rpcAddr γ.W masterAddr ∗
    ([∗list] a ∈ replicaRpcAddrs, net.rpc.rpcAddr γ.W a) ∗
    ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
    net.rpc.codecSet ∗ net.rpc.kitCodecOk ∗
    ([∗list] a ∈ replicaAddrs, addrProto a (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem)) ∗
    sp.inv γ.sp γ.conf γ.mem γ.lin)

instance nodeEnv_persistent (γ : SwiftNames netDistGF) : Persistent (nodeEnv γ) := by
  unfold nodeEnv; infer_instance

/-- `s` is client node `c`'s `*Sys`: its read-only fields hold the addresses and the
configuration `cf` (with `conf.is γ cf`); its mutex guards `done`; the node's ghost is claimed. -/
def isSysL (γ : SwiftNames netDistGF) (c : Nat) (s : Loc) : IProp netDistGF :=
  iprop(∃ (cf : Conf) (asl : GoSlice),
    s.[examples.swiftnet.Sys, go!"addrs"] ↦□ asl ∗ asl ↦*□ addrs ∗
    s.[examples.swiftnet.Sys, go!"conf"] ↦□ confV cf ∗ conf.is γ cf ∗
    sync.isMutex (s.[examples.swiftnet.Sys, go!"mu"])
      (∃ d : w64, s.[examples.swiftnet.Sys, go!"done"] ↦ d) ∗
    nodeEnv γ ∗ client.nodeGhostOk γ.sp (sp.PNode.cl c))

instance isSysL_persistent (γ : SwiftNames netDistGF) c s : Persistent (isSysL γ c s) := by
  unfold isSysL; infer_instance

/-- The interface value of the node's `*Sys` at `s`. -/
def sysV (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType examples.swiftnet.Sys.ty) #s

/-- `sys` is client node `c`'s `*Sys`. -/
def isSys (γ : SwiftNames netDistGF) (c : Nat) (sys : GoInterface) : IProp netDistGF :=
  iprop(∃ s : Loc, ⌜sys = sysV s⌝ ∗ isSysL γ c s)

instance isSys_persistent (γ : SwiftNames netDistGF) c sys : Persistent (isSys γ c sys) := by
  unfold isSys; infer_instance

/-- The node's client (`s.b`) before its operation `j`. -/
def clSt (γ : SwiftNames netDistGF) (s : Loc) (c : Nat) (j : Nat) : IProp netDistGF :=
  iprop((s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗ sp.clientSeq γ.sp (cidOf c) 0) ∨
    ∃ (b : Loc) (sq : Nat), s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null ∧ sq ≤ j⌝ ∗
      client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) sq)

/-- Client `c`'s token before its operation `j` (`ClientNodeSpec.client_tok`). -/
def clientTok (γ : SwiftNames netDistGF) (c : Nat) (sys : GoInterface) (j : Nat) :
    IProp netDistGF :=
  iprop(∃ s : Loc, ⌜sys = sysV s⌝ ∗ clSt γ s c j)

theorem clSt_advance (γ : SwiftNames netDistGF) (s : Loc) (c j j' : Nat) (h : j ≤ j') :
    clSt γ s c j ⊢ clSt γ s c j' := by
  unfold clSt
  iintro (H | ⟨%b, %sq, Hb, %Hb, Hr⟩)
  · ileft; iexact H
  · iright
    iexists b, sq
    iframe Hb Hr
    ipureintro; exact ⟨Hb.1, by omega⟩

theorem clientTok_advance (γ : SwiftNames netDistGF) (c : Nat) (sys : GoInterface)
    (j j' : Nat) (h : j ≤ j') : clientTok γ c sys j ⊢ |==> clientTok γ c sys j' := by
  unfold clientTok
  iintro ⟨%s, %Hs, H⟩
  imodintro
  iexists s
  isplitr
  · ipureintro; exact Hs
  iapply clSt_advance γ s c j j' h $$ H

end defs

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
