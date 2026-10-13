/- Proof of `Spec/go_etcd_io/raft/v3/RawNode__ProposeConfChange.lean`, Lean-first
(2026-10-13). As `RawNode.Propose`'s, on `confChangeToMsg`'s message; the entry's data is
recorded as proposed (`propRegister`), which gives its `entData` (`entData_cc`) and the
bytes `Step` needs (`ccEntsOk_cc`). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.confChangeToMsg
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

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [ccPropMsg, MsgHup, MsgVote,
  MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,
  MsgSnap, MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp,
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

theorem RawNode.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %esl %data %bs ⟨Hc, Hes, Hcap, Hdata, %Hbs⟩
  ipersist Hdata
  iunfold propRegister at Hreg
  imod Hreg $$ %data %bs Hdata with #Hpd
  ihave #Hent := entData_cc γ o data bs Hbs $$ Hpd
  ihave #Hcc := ccEntsOk_cc o data bs Hbs $$ Hdata
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step γ.reCfg γ _ id s ps (ccPropMsg esl) [ccEntry (some o) data] [] rfl
    (by simp [StepMsg, stepMsgTypes, ccPropMsg, MsgProp]) (fun _ => Hin)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne)
    (fun _ => ⟨rfl, .inl rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hrel
    $$ [$Hphys $Hghost Hes Hcap Hcr]
  · -- the message: its one-entry batch, owned, with the entry's bytes; `Context` nil
    simp only [ccPropMsg, MsgProp, ite_true]
    isplitl [Hes Hcap]
    · simp only [named]
      isplitl [Hes]
      · iframe Hes
        iexists [some o]
        iexact Hcc
      isplitl [Hcap]
      · iexact Hcap
      isplitr
      · ipureintro
        intro _
        exact ⟨List.cons_ne_nil _ _, by simp⟩
      isplitr
      · ipureintro
        intro Hc
        simp [MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty _
        rw [show mtypeOf (W32 2) = some .propose from rfl] at Hty
        cases Hty
        unfold isMessage absMsg absMsgFrom
        isplitr
        · ipureintro
          exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entData (GF := GF) γ e)).2
        iexact Hent
    isplitr
    · iapply ownSlice_nil
    isplitl [Hcr]
    · have H215 : ¬ ((W32 2 : w32) = W32 15) := by word
      simp only [MsgReadIndex, H215, ite_false]
      iexact Hcr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
  simp only [ccPropMsg, MsgProp, ite_true]
  iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Hloc, %_, %_, %_, Herr⟩
  wp_auto
  -- what the `RawNode` tracks is kept: `LocalStepOk`, and the commit index does not move
  -- back (`Step.commit_mono`)
  obtain ⟨Hfr, Hap⟩ := Hloc (.inl rfl)
  have Hap' := Hap (fun Hc => absurd Hc (by msg_ne))
  have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
    obtain ⟨recv, Hst⟩ := Href
    have H := Step.commit_mono Hst
    rw [← Hrel.1, ← Hrel'.1] at H
    exact H
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hfr.2.2.2.2.1
    Hfr.2.2.2.2.2.1 $$ Hstrecs
  iapply HΦ
  simp only [named]
  iframe Hc
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpown]
  · iapply ownRawNode_intro γ rn id rs s' ps' rnv sv steps Hrel' Hin Hasync
      (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp)
      (by rw [Hfr.2.2.2.1]; exact Hsnap)
      (stepsOk_mono s s' _ Hfr.1 ⟨Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1⟩ Hc Hap'
        Hfr.2.2.2.2.2.2.2.1 Hstok)
      (by rw [Hfr.1]; exact Htrm) (by rw [Hfr.2.2.2.2.2.2.1]; exact Hstor)
      (by rw [Hfr.2.2.2.2.2.2.2.1]; exact Hpvoff)
      (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_out) (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_unst)
      (Int.le_trans Hrs_clb Hc)
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'
  icases Herr with (%Herr | ⟨-, #Hd⟩)
  · ileft; ipureintro; exact Herr
  · iright; iexact Hd

end proof

end EtcdGrove
end Perennial
