/-
The definitions, specs and lemmas of `Readers.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.UnmarshalDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleReplyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.TableC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.LatencyTable__WaitDurationDefs
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

open swift.handler

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- An `MReply` on `replyChan`. -/
def repP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (x : sp.CmdId) (l : Loc),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l⌝ ∗ replyArg H x l)

/-- An `MLightSlowAck` on `lightSlowAckChan`. -/
def lsP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (x : sp.CmdId) (l : Loc),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l⌝ ∗ lsArg H x l)

/-- An `MFastAckClient` on `fastAckClientChan`. -/
def facP (H : HC) (v : GoInterface) : IProp netDistGF :=
  iprop(∃ (l : Loc) (fac : swift.MFastAckClient) (hs : List sp.Hash),
    ⌜v = interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l ∧ sp.cw.hashOk hs ∧
      (cmdOf fac.CmdId').cl = H.cid⌝ ∗
    l ↦□ fac ∗ fac.Checksum' ↦*□ hs.map shashOf ∗
    sp.msgOk H.γ H.γc H.γm (.fastAckClient fac.Replica' fac.Ballot' (cmdOf fac.CmdId') hs))

instance repP_persistent H v : Persistent (repP H v) := by unfold repP; infer_instance
instance lsP_persistent H v : Persistent (lsP H v) := by unfold lsP; infer_instance
instance facP_persistent H v : Persistent (facP H v) := by
  unfold facP; haveI := sp.msgOk_persistent (γ := H.γ) (γc := H.γc) (γm := H.γm); infer_instance

/-- One replica's reader: none, or a connection of kind `client cid` with its reader at the
stream's start. -/
def rdEnd (H : HC) (rd : Loc) : IProp netDistGF :=
  iprop(⌜rd = null⌝ ∨ ∃ (srv : GoInterface) (c : Nat),
    bufio.readerOk srv (recvTokL c false (sp.outQ H.γ H.γc H.γm)) ∗
    sp.connKind H.γ c (.client H.cid) ∗
    bufio.ownReader rd srv (recvTokL c false (sp.outQ H.γ H.γc H.γm)) [])

/-- The client's table, read-only: the three client messages' entries, their channels'
protocols. -/
def tblOk (H : HC) (t : Loc) : IProp netDistGF :=
  iprop(∃ (M : GMap w8 rpc.Pair') (o1 o2 o3 : Loc) (ch1 ch2 ch3 : Loc) (g1 g2 g3 : ChanNames),
    rpc.tblRO t M ∗
    ⌜M !! W8 10 = some ⟨interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #o1, ch1⟩ ∧
      M !! W8 12 = some ⟨interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #o2, ch2⟩ ∧
      M !! W8 15 = some ⟨interface.mkOk (go.GoType.PointerType swift.MReply.ty) #o3, ch3⟩⌝ ∗
    isChanBag g1 ch1 (facP H) ∗ isChanBag g2 ch2 (lsP H) ∗ isChanBag g3 ch3 (repP H))

instance tblOk_persistent H t : Persistent (tblOk H t) := by unfold tblOk; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- `c.RegisterRPCTable(t)` on the client's struct `cl`: a reader per connected replica. -/
abbrev RegisterRPCTable.specI : Prop :=
  ∀ (H : HC) (cl t : Loc) (rsl rpsl : GoSlice) (rds : List Loc) (l : List GoString)
    (ov : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.time ∗
      structFieldRef client.Client go!"readers" cl ↦□ rsl ∗ rsl ↦*□ rds ∗
      structFieldRef client.Client go!"replicas" cl ↦□ rpsl ∗ rpsl ↦*□ l ∗
      structFieldRef client.Client go!"dt" cl ↦□ null ∗
      globalAddr swift.errVarintOverflow ↦□ ov ∗ ⌜ov ≠ interface.nil ∧ rds.length = l.length⌝ ∗
      tblOk H t ∗ [∗list] rd ∈ rds, rdEnd H rd }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"RegisterRPCTable")) (Val #t))
  {{ RET #(); True }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MFastAckClient (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l);
        l ↦ (zero_val swift.MFastAckClient) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MLightSlowAck (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MLightSlowAck.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l);
        l ↦ (zero_val swift.MLightSlowAck) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] [client.Assumptions]
  [time.Assumptions] [dlog.Assumptions] [bytes.Assumptions] [io.Assumptions]
  [errors.Assumptions] [bufio.Assumptions] [rpc.Assumptions] [replica.defs.Assumptions] in
theorem wp_New_MReply (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MReply.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l);
        l ↦ (zero_val swift.MReply) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

end proof

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos
