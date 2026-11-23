/-
Package `proxy`: the internal specs of `Proxy.NetworkInit`'s routines (`proxynetwork.go`), proved
in `Net*.lean`, and the unpacking of `proxyShared` they share.
-/
module

public import Dsverify.Proof.raxos.Replica
public import Dsverify.Proof.raxos.Proxy.WireProof
public import Dsverify.Proof.raxos.Cons.Laws
public import Harness.Proof.bufio.Net
public import Harness.Proof.bufio.ReadFull
public import Harness.Proof.net.Listen
public import Harness.Proof.net.TCPListener__Accept
public import Harness.Proof.net.Dial
public import Harness.Proof.net.TCPConn__Write
public import Harness.Proof.net.TCPConn__Close
public import Harness.Proof.fmt.Extra
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section names
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]

/-- Client `cl`'s peer name, as `connectToClient`'s map keys see it. -/
theorem peer_w64 (cl : Nat) (hcl : cl < 6) : W64 (sint.Z (W32 (21 + cl))) = W64 (21 + cl) := by
  rcases cl with _ | _ | _ | _ | _ | _ | cl <;> first | rfl | omega

/-- Client `cl`'s handshake. -/
theorem hs_client (cl : Nat) (hcl : cl < 6) : hs (21 + cl) = [W8 (21 + cl), W8 0, W8 0, W8 0] := by
  rcases cl with _ | _ | _ | _ | _ | _ | cl <;> first | rfl | omega

/-- The accept routine's decoding of client `cl`'s handshake. -/
theorem hs_decode (cl : Nat) (hcl : cl < 6) :
    W32 (uint.Z (W16 (uint.Z (W8 (21 + cl))) ||| W16 (uint.Z (W8 0)) <<< W64 8)) = W32 (21 + cl) := by
  rcases cl with _ | _ | _ | _ | _ | _ | cl <;> first | decide | omega

end names

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
 
  [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

/-- `pr.internalSendMessage(peer, rp)` for an answer `rp` (as `outP` gives it: client `cl`'s
request `x`'s result `r`; whether it can be encoded is learned at its `Marshal`, P4). -/
abbrev internalSendMessage.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (peer : w64) (rp : raxos.common.RPCPair) (l : Loc)
    (cl : Nat) (x r : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr ∗
      ⌜rp.Code' = W8 1 ∧
        rp.Obj' = interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #l⌝ ∗
      repCB l .discard ⟨x, clientName cl, [r]⟩ ∗ opAns γ x r }}
    (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"internalSendMessage"))
      (Val #peer)) (Val #rp))
  {{ RET #(); True }}

/-- `pr.startOutgoingLinks()`: the 200 senders. -/
abbrev startOutgoingLinks.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"startOutgoingLinks")) (Val #()))
  {{ RET #(); True }}

/-- `pr.connectionListener(br, 21 + cl)`: the reader of a connection accepted on the proxy's
port, after client `cl`'s handshake, no frame read yet. -/
abbrev connectionListener.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr br : Loc) (cv : GoInterface) (cid : w64) (cl : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr ∗
      net.rpc.connIface cv cid true ∗
      bufio.ownReader br cv (recvTok cid true (proxyInProto γ k)) (hs (21 + cl)) ∗ rdCtr γ cid 0 }}
    (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"connectionListener"))
      (Val #br)) (Val #(W32 (21 + cl))))
  {{ RET #(); True }}

/-- `pr.connectToClient(21 + cl)`: dial client `cl` back, publish the writer. -/
abbrev connectToClient.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (cl : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr ∗ ⌜cl < 6⌝ }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"connectToClient"))
      (Val #(W32 (21 + cl))))
  {{ RET #(); True }}

/-- `pr.waitForConnections()`: the accept routine. -/
abbrev waitForConnections.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr ∗
      addrTok (proxyAddr k) ∗ nodeIp (ipOf k) }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"waitForConnections")) (Val #()))
  {{ RET #(); True }}

end specs

section unpack
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions]

/-- What the network routines use of `proxyShared`. -/
theorem proxyShared_net (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) :
    proxyShared (GF := GF) γ c k pr ⊢
      sharedFacts γ c k ∗ sharedConsts c k pr ∗ sharedChans γ k pr ∗ sharedLoop γ k pr ∗
      sharedNet γ k pr := by
  unfold proxyShared proxySharedDef
  iintro ⟨%_hs, %γs, %cb, %bm, %ebm, #Hf, #Hc, -, #Hch, #Hl, #Hn⟩
  iframe Hf Hc Hch Hl Hn

end unpack

end Perennial.raxos
