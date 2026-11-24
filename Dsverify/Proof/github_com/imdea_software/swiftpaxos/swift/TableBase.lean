/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableBase.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift replica's table entries (`sp.newOk`, `sp.unmarshalOk` at `swift.msgRep`): the generic
part and the fixed-size messages.

* `swift.tbl.newOk_of`: an entry's `newOk` from its `New`'s spec and its fresh objects'
  `unmarshalOk` (under persistent facts `Ctx`);
* `swift.tbl.unmarshalOk_vacuous`: a type no well-formed message has (the stream law says the
  next bytes are of such a message);
* `MNewLeader.Unmarshal` (8 bytes), `MLightSlowAck.Unmarshal` (16 bytes, the client's proof),
  their `unmarshalOk`;
* the `New` methods allocating a zero struct.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MsgRep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.UnmarshalDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.StreamLaw

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section generic
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- An entry's `newOk` from its `New`'s spec (fresh objects `P l`) and their `unmarshalOk`. -/
theorem newOk_of (c : w8) (Rep : GoInterface → sp.Msg → IProp netDistGF) (ty : go.GoType)
    (o : Loc) (Ctx : IProp netDistGF) [Persistent Ctx] (P : Loc → IProp netDistGF)
    (hnew : {{ Ctx }} (App (Val (o @!! go.GoType.PointerType ty @!! go!"New")) (Val #()))
      {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType ty) #l); P l }})
    (hun : ∀ l : Loc, Ctx ∗ P l ⊢ sp.unmarshalOk c Rep (interface.mkOk (go.GoType.PointerType ty) #l)) :
    Ctx ⊢ sp.newOk c Rep (interface.mkOk (go.GoType.PointerType ty) #o) := by
  iintro #Hctx
  unfold sp.newOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply hnew $$ Hctx
  inext
  iintro %l Hl
  iapply HΦ
  iapply hun l $$ [$Hctx $Hl]

/-- No well-formed message has type `c`: the entry's `Unmarshal` is never reached on a stream
of the protocol (its stream law is false). -/
theorem unmarshalOk_vacuous (c : w8) (hc : ∀ m : sp.Msg, m.code ≠ c)
    (Rep : GoInterface → sp.Msg → IProp netDistGF) (e : GoInterfaceOk) :
    ⊢ sp.unmarshalOk c Rep (interface.ok e) := by
  unfold sp.unmarshalOk
  iexists e
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ - #Hlaw Hown -
  ihave Hown : bufio.ownReader br rd I (R ++ []) $$ [Hown]
  · iExactEq Hown; simp
  unfold sp.streamLaw
  icases Hlaw $$ %([] : List w8) Hown with ⟨-, >%H⟩
  obtain ⟨m, w, -, -, hcm, -⟩ := H
  exact absurd hcm (hc m)

end generic

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
