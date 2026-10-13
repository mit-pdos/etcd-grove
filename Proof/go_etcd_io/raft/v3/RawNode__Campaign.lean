/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Campaign
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

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message `pb.Message{Type: MsgHup}`; its `NetFrame` and
`TermStep` keep `ownRawNode` but for the term (`stepsOk_mono_le`). -/
theorem RawNode.Campaign.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Campaign.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hterm
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps _ [] [] rfl
    (by simp [StepMsg, stepMsgTypes, MsgHup]) Hin
    (fun _ => ⟨rfl, by rw [← Htrm]; exact Hterm⟩)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hrel
    $$ [$Hphys $Hghost Hcr]
  · -- the message: no entries, no `Context`, no snapshot
    have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
    simp only [hP, ↓reduceIte, named]
    isplitr
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; msg_ne
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 0) = none from rfl] at Hty
      cases Hty
    isplitr
    · iapply ownSlice_nil
    isplitl [Hcr]
    · rw [if_neg (by msg_ne)]; iexact Hcr
    imodintro
    iintro %Hc
    simp [MsgSnap] at Hc
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  simp only [hP, ↓reduceIte]
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, -, Herr⟩
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by msg_ne) (by msg_ne)
  obtain ⟨Ht1, Ht2, -, -⟩ := Htm (by msg_ne)
  have Ht2 := Ht2 rfl
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ $$ %err %s'.term
    simp only [named]
    isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpown]
    · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' ps' rnv sv steps Hrel' Hin
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok) rfl (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'
    ipureintro
    rw [Htrm]
    exact ⟨⟨Ht1, Ht2⟩, Herr⟩
  · exfalso; revert Hc'; msg_ne

end proof

end EtcdGrove
end Perennial
