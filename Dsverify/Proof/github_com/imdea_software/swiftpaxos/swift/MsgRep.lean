/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MsgRep.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift replica's message table (`initCs`'s fourteen registrations) as the replica group's
`sp.tableOk` sees it: the representation `swift.msgRep c o m` of a decoded message `m` by the
object `o` its type's `Unmarshal` filled, and the bags `swift.csBags` of the fourteen channels
(what the replica's peer readers send on them: `sp.chanMsgP … (swift.msgRep c)`).

The representations are the natural owned ones (the struct owned, its slices owned), except
where the run loop hands the object to a consumer that takes read-only slices:

* `MFastAck` (9): `swift.fastAckRepr` (its slices `↦*□`), as `handleFastAck` and the batcher
  take it; `MLightSlowAck` (12): `swift.slowAckRepr`;
* `MAcks` (13): the two slices owned, each fast ack's `fastAckRepr`, each slow ack's
  `slowAckRepr` (the batcher's `MAcks.marshalH` shape); `MOptAcks` (14): the acks' slice owned,
  each `swift.ackRepr`;
* `MFastAckClient` (10), `MReply` (15): the client's shapes (owned slices);
* `MNewLeader` (16): the struct; `MNewLeaderAckN` (17): the struct and its four slices owned,
  entry `i`'s command's value and dependencies owned (the shape of `swift.ackObj`, owned);
* `MSync` (18): the codec's `structOwn` of the decoded value; it is the message's own when the
  wire value's map listings have distinct keys (`KitVal.wf`, which the codec's `dec` needs: the
  message's witness `syncWireOk` with the ballot's `MSync` having distinct ids gives it);
* the five types no peer sends (`MSlowAck` 11, `MPing` 19, `MPingRep` 20, `MCollect` 21,
  `MAccept` 22): no model message has their code, so their representation is never used
  (`False`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The names of the fourteen channels' bags. -/
structure swift.CsNames where
  fastAck : ChanNames
  fastAckClient : ChanNames
  slowAck : ChanNames
  lightSlowAck : ChanNames
  acks : ChanNames
  optAcks : ChanNames
  reply : ChanNames
  newLeader : ChanNames
  newLeaderAckN : ChanNames
  sync : ChanNames
  ping : ChanNames
  pingRep : ChanNames
  collect : ChanNames
  accept : ChanNames

namespace sp

/-- A permuted listing of a map stays a listing of `M`. -/
theorem perm_some {A : Type} {o o' : Option (List A)} {l t : List A} (ho : o = some l)
    (hp : l.Perm t) (hr : Option.Rel List.Perm o o') : ∃ l', o' = some l' ∧ l'.Perm t := by
  subst ho
  cases hr with
  | some h => exact ⟨_, rfl, h.symm.trans hp⟩

/-- `syncWireOk` is closed under the encoder's reorderings of the maps. -/
theorem syncWireOk_equiv {m m' : SyncWire} {M : SyncMsg} (h : syncWireOk m M)
    (he : KitVal.equiv (.msync m) (.msync m')) : syncWireOk m' M := by
  obtain ⟨⟨ps, hp, hpp⟩, ⟨cs, hc, hcp⟩, ⟨ds, hd, hdp⟩⟩ := h
  obtain ⟨-, -, h1, h2, h3⟩ := he
  exact ⟨perm_some hp hpp h1, perm_some hc hcp h2, perm_some hd hdp h3⟩

end sp

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- An `MNewLeaderAckN` entry's command and dependencies (owned). -/
def swift.repEntryOwn (cm : state.Command) (sd : swift.SDep) (e : sp.RepEntry) :
    IProp netDistGF :=
  iprop(∃ vs : GoSlice, ⌜cm = state.Command.mk e.cmd.op e.cmd.key vs⌝ ∗ vs ↦* e.cmd.val ∗
    sd.Dep' ↦* (e.dep.map ofCmdId))

/-- The object `o` represents the message `m` (see the file header; by `m`'s constructor, the
code being `m.code` in the table's entries). -/
def swift.msgRepM (o : GoInterface) : sp.Msg → IProp netDistGF
  | .fastAck f => iprop(∃ (l : Loc) (fa : swift.MFastAck),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ ∗ l ↦ fa ∗
      swift.fastAckRepr fa f)
  | .fastAckClient r b x cs => iprop(∃ (l : Loc) (csl : GoSlice),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l⌝ ∗
      l ↦ swift.MFastAckClient.mk r b (ofCmdId x) csl ∗ csl ↦* cs.map swift.handler.shashOf)
  | .lightSlowAck s => iprop(∃ (l : Loc) (sa : swift.MLightSlowAck),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l⌝ ∗ l ↦ sa ∗
      ⌜swift.slowAckRepr sa s⌝)
  | .acks fs ss => iprop(∃ (l : Loc) (fsl ssl : GoSlice)
        (fps : List (swift.MFastAck × sp.FastAck)) (sps : List (swift.MLightSlowAck × sp.SlowAck)),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #l ∧
        fps.map Prod.snd = fs ∧ sps.map Prod.snd = ss ∧ ∀ p ∈ sps, swift.slowAckRepr p.1 p.2⌝ ∗
      l ↦ swift.MAcks.mk fsl ssl ∗ fsl ↦* fps.map Prod.fst ∗ ssl ↦* sps.map Prod.fst ∗
      [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2)
  | .optAcks r b al => iprop(∃ (l : Loc) (asl : GoSlice) (ps : List (swift.Ack × sp.Ack)),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #l ∧ ps.map Prod.snd = al⌝ ∗
      l ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst ∗
      [∗list] p ∈ ps, swift.ackRepr p.1 p.2)
  | .reply r b x cs v => iprop(∃ (l : Loc) (csl vsl : GoSlice),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l⌝ ∗
      l ↦ swift.MReply.mk r b (ofCmdId x) csl vsl ∗ csl ↦* cs.map swift.handler.shashOf ∗
      vsl ↦* v)
  | .newLeader r b => iprop(∃ l : Loc,
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #l⌝ ∗
      l ↦ swift.MNewLeader.mk r b)
  | .newLeaderAckN r b c es => iprop(∃ (l : Loc) (ids ph cm dp : GoSlice)
        (cmL : List state.Command) (dpL : List swift.SDep),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #l⌝ ∗
      l ↦ swift.MNewLeaderAckN.mk r b c ids ph cm dp ∗
      ids ↦* (es.map (fun e => ofCmdId e.id)) ∗ ph ↦* (es.map (·.phase)) ∗ cm ↦* cmL ∗
      dp ↦* dpL ∗ ⌜cmL.length = es.length ∧ dpL.length = es.length⌝ ∗
      [∗list] i ↦ e ∈ es, ∃ (cc : state.Command) (sd : swift.SDep),
        ⌜cmL[i]? = some cc ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryOwn cc sd e)
  -- the real `encoding/gob`'s decoding (Spec/encoding/gob/Decoder__Decode.lean): `m` up to its
  -- maps' order
  | .sync m _ => iprop(∃ (l : Loc) (m' : sp.SyncWire),
      ⌜o = interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l ∧
        sp.KitVal.equiv (.msync m) (.msync m')⌝ ∗
      structOwn swift.MSync.ty l (DFrac.own 1) (.msync m'))
  | _ => iprop(False)

/-- The representation of the table's type `c` (`sp.tableOk`'s `Rep`): `msgRepM` (the code is
`m.code`, which `sp.chanMsgP` says). -/
def swift.msgRep (_c : w8) (o : GoInterface) (m : sp.Msg) : IProp netDistGF :=
  swift.msgRepM o m

/-- The persistent bags of the fourteen channels (see the file header). -/
def swift.csBags (γ : sp.Names) (γc γm : GName) (v : swift.CommunicationSupply)
    (n : swift.CsNames) : IProp netDistGF :=
  iprop(isChanBag n.fastAck v.fastAckChan' (sp.chanMsgP γ γc γm (W8 9) (swift.msgRep (W8 9))) ∗
    isChanBag n.fastAckClient v.fastAckClientChan'
      (sp.chanMsgP γ γc γm (W8 10) (swift.msgRep (W8 10))) ∗
    isChanBag n.slowAck v.slowAckChan' (sp.chanMsgP γ γc γm (W8 11) (swift.msgRep (W8 11))) ∗
    isChanBag n.lightSlowAck v.lightSlowAckChan'
      (sp.chanMsgP γ γc γm (W8 12) (swift.msgRep (W8 12))) ∗
    isChanBag n.acks v.acksChan' (sp.chanMsgP γ γc γm (W8 13) (swift.msgRep (W8 13))) ∗
    isChanBag n.optAcks v.optAcksChan' (sp.chanMsgP γ γc γm (W8 14) (swift.msgRep (W8 14))) ∗
    isChanBag n.reply v.replyChan' (sp.chanMsgP γ γc γm (W8 15) (swift.msgRep (W8 15))) ∗
    isChanBag n.newLeader v.newLeaderChan' (sp.chanMsgP γ γc γm (W8 16) (swift.msgRep (W8 16))) ∗
    isChanBag n.newLeaderAckN v.newLeaderAckNChan'
      (sp.chanMsgP γ γc γm (W8 17) (swift.msgRep (W8 17))) ∗
    isChanBag n.sync v.syncChan' (sp.chanMsgP γ γc γm (W8 18) (swift.msgRep (W8 18))) ∗
    isChanBag n.ping v.pingChan' (sp.chanMsgP γ γc γm (W8 19) (swift.msgRep (W8 19))) ∗
    isChanBag n.pingRep v.pingRepChan' (sp.chanMsgP γ γc γm (W8 20) (swift.msgRep (W8 20))) ∗
    isChanBag n.collect v.collectChan' (sp.chanMsgP γ γc γm (W8 21) (swift.msgRep (W8 21))) ∗
    isChanBag n.accept v.acceptChan' (sp.chanMsgP γ γc γm (W8 22) (swift.msgRep (W8 22))))

instance swift.csBags_persistent (γ : sp.Names) (γc γm : GName) (v : swift.CommunicationSupply)
    (n : swift.CsNames) : Persistent (swift.csBags γ γc γm v n) := by
  unfold swift.csBags; infer_instance

end defs

end Perennial.github_com.imdea_software.swiftpaxos
