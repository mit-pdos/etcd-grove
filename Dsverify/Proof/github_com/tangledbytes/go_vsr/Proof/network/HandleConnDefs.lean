/-
The definitions, specs and lemmas of `HandleConn.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Ghost
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Perennial.Proof.sync.Results
public import Net.Spec.net.Conn__Close

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- An event type as a log argument: a named `uint8` without formatting methods. -/
theorem network.evType_arg (t : w8) :
    fmt.IntArgValue (interface.mk events.EventType.ty #t) (uint.Z t) := by
  have hu : underlying events.EventType.ty = go.uint8 := by
    rw [go.UnderlyingDirectedEq.underlying_unfold (t := events.EventType.ty)]
    exact go.is_underlying
  refine .named _ _ _ ?_ (by rw [hu]; simp [fmt.IsIntType]) (fmt.NoFmtMethods.of_methodSetIs_nil _)
    (by rw [hu]; exact .uint8 t)
  unfold fmt.IsIntType events.EventType.ty
  simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16,
    go.uint8]

/-- `tcp.handleConn(conn, key, src)`: reads `conn`'s events (from `src`, an `addrOk` source) into
the queue (an `addrOkN` source) until the connection fails; then closes it and removes it from the map. -/
abbrev network.TCP.handleConn.spec : Prop :=
  ∀ (tcp : Loc) (ns : network.TcpNames) (v : network.TCP) (c : Loc) (cid : Nat) (side : Bool)
    (a : GoString) (la ra : GoInterface) (key : GoString) (src : ipv4port.IPv4Port),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.tcpCore tcp ns v ∗ network.readerOk ns.sys ∗ net.connAt c cid side a la ra ∗
      recvTok (Gg := hG.goose_globalGS) cid side (VsrWire.protoOf ns.sys) [] ∗
      network.addrOkN ns src }}
    (App (App (App (Val (tcp @!! go.GoType.PointerType network.TCP.ty @!! go!"handleConn"))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c))) (Val #key)) (Val #src))
  {{ RET #(); True }}

/-- The reader's token, and the connection is the library's. -/
theorem network.recvTok_connIs' (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTok (Gg := hG.goose_globalGS) cn s P R ⊢ recvTok cn s P R ∗ connIs cn :=
  persistent_entails_left (recvTok_connIs cn s P R)

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
