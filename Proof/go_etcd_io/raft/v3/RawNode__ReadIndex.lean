/- Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): the message is a fresh `&pb.Message{Type: MsgReadIndex.Enum(),
Entries: []*pb.Entry{{Data: rctx}}}`: the entry (`propEntryM c`, the context's frozen bytes)
allocated by the slice literal and frozen; the message `msgIn` with its entries read-only.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ReadIndex
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgReadIndex` (`W32 15`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message `pb.Message{Type: MsgReadIndex, Entries: []pb.Entry{{Data:
rctx}}}`: its abstraction is the client's request (`isPropData`, `readReq`), and it carries
the client's credit; `NetFrame` and `TermStep` keep `ownRawNode` (the term does not move:
the message's is `0`). -/
theorem RawNode.ReadIndex.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.ReadIndex.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rctx c Qr L0
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the deposit (2026-10-14, stage R): the update fired at the global committed log `Lc`
  ihave #Hcinv := ownStepGhost_inv γ _ cf id s $$ Hghost
  imod read_deposit γ c Qr L0 $$ Hcinv Hfr Hau HL0 with ⟨%Lc, %HL0c, #Hrq, #Hrd⟩
  wp_auto_lc 1
  rw [show raftpb.MsgReadIndex = #((W32 15 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 15) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #rctx)])] = 1 := rfl
  simp only [Hsz]
  -- the request's entry: its data the context's bytes, frozen
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, null, rctx, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM c) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hctx
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod entOwn_freeze $$ He with #He
  imod ownSlice_persist $$ Hsl with #Hsl
  wp_auto
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct «$a0_ptr» (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) DFrac.discard false [l0]
      ⟨{ (zero_val MessageM) with Type' := W32 15 }, [propEntryM c], none, [], []⟩
      ⊤ rfl $$ [«$a0»] with Hm
  · iframe «$a0» Hsl Hnilb cTy
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  have HmC : needsCap ({ (zero_val MessageM) with Type' := W32 15 } : MessageM) = false := rfl
  have hP : (W32 15 : w32) ≠ MsgProp := by simp [MsgProp]
  have hR : (W32 15 : w32) = MsgReadIndex := rfl
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 15 } : MessageM)
    [propEntryM c] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgReadIndex])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (fun _ => rfl)
    (by msg_ne) (by msg_ne) (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hm Hcred]
  · -- the message: its one-entry batch, read-only; `Context` nil; the client's request
    simp only [hP, ↓reduceIte, named]
    isplitl [Hm]
    · isplitl [Hm]
      · simp only [msgIn, HmC]; iexact Hm
      isplitr
      · iempintro
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; msg_ne
      imodintro
      iintro %ty %Hty _
      rw [show mtypeOf (W32 15) = some .readIndex from rfl] at Hty
      cases Hty
      unfold isMessage absMsg absMsgFrom
      iexists propEntryM c, c, Lc
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iframe Hrq
    isplitl [Hcred]
    · rw [ite_eq_left hR]; iexact Hcred
    imodintro
    iintro %Hc
    exfalso
    revert Hc
    msg_ne
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, -, -⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne))
  obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
  have H0 : uint.Z (zero_val MessageM).Term' = 0 := rfl
  simp only [H0] at Ht3
  -- the term does not move: the message's is `0`
  have Hterm : s'.term = s.term := by
    have h0 : 0 ≤ uint.Z s.term := by word
    rw [Int.max_eq_left h0] at Ht3
    word
  have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn Hsd (Hip4 (by msg_ne)) $$ Hstrecs
  ihave #Hpost : iprop(∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗ isRead γ c Qr) $$ []
  · iexists Lc
    iframe Hrq Hrd
    ipureintro; exact HL0c
  iapply HΦ
  simp only [named]
  iframe Hpost
  iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin Hal
    Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
    Hstok' (by rw [Hterm]; exact Htrm) (by rw [Hsg]; exact Hstor) 
    (Hpvoff.step rfl rfl Hpre Hgh (by rw [Hterm]; exact Hpvoff.2.2.1) Hpcs (by msg_ne))
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' Hsd Hu Ha Hc)
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc

end proof

end EtcdGrove
end Perennial
