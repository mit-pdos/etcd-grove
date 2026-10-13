/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ReadIndex
public import Spec.go_etcd_io.raft.v3.raft__Step
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
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message `pb.Message{Type: MsgReadIndex, Entries: []pb.Entry{{Data:
rctx}}}`: its abstraction is the client's request (`isPropData`, `readReq`), and it carries
the client's credit; `NetFrame` and `TermStep` keep `ownRawNode` (the term does not move:
the message's is `0`). -/
theorem RawNode.ReadIndex.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.ReadIndex.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rctx c Lc Hsing
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply wp_slice_literal (l := [({ (zero_val raftpb.Entry) with Data' := rctx } :
    raftpb.Entry)])
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hes, Hcap⟩
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  wp_auto
  have hP : (W32 15 : w32) ≠ MsgProp := by simp [MsgProp]
  have hR : (W32 15 : w32) = MsgReadIndex := rfl
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps _
    [({ (zero_val raftpb.Entry) with Data' := rctx } : raftpb.Entry)] [] rfl
    (by simp [StepMsg, stepMsgTypes, MsgReadIndex]) (fun _ => Hin)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (fun _ => ⟨rfl, Hsing⟩) (by msg_ne) (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hrel
    $$ [$Hphys $Hghost Hcap Hcred]
  · -- the message: its one-entry batch, read-only; `Context` nil; the client's request
    simp only [hP, ↓reduceIte, named]
    isplitl [Hcap]
    · isplitr
      · iexact Hes
      isplitl [Hcap]
      · iexact Hcap
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; msg_ne
      imodintro
      iintro %ty %Hty _
      rw [show mtypeOf (W32 15) = some .readIndex from rfl] at Hty
      cases Hty
      unfold isMessage absMsg absMsgFrom
      iexists ({ (zero_val raftpb.Entry) with Data' := rctx } : raftpb.Entry), c, Lc
      isplitr
      · ipureintro; rfl
      iframe Hpd Hrq
    isplitr
    · iapply ownSlice_nil
    isplitl [Hcred]
    · rw [if_pos hR]; iexact Hcred
    imodintro
    iintro %Hc
    exfalso
    revert Hc
    msg_ne
  simp only [hP]
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, -, -⟩
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by msg_ne) (by msg_ne)
  obtain ⟨Ht1, -, Ht3, -⟩ := Htm (by msg_ne)
  have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
  have H0 : uint.Z (0 : w64) = 0 := rfl
  simp only [H0] at Ht3
  -- the term does not move: the message's is `0`
  have Hterm : s'.term = s.term := by
    have h0 : 0 ≤ uint.Z s.term := by word
    rw [Int.max_eq_left h0] at Ht3
    word
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
  iapply HΦ
  simp only [named]
  iapply ownRawNode_intro γ rn id rs s' ps' rnv sv steps Hrel' Hin
    Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
    Hstok' (by rw [Hterm]; exact Htrm) (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'

end proof

end EtcdGrove
end Perennial
