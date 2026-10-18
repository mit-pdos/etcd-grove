/- Lean-first (no Rocq counterpart). 
raft v3.7 (2026-10-16, stage R5): the message is a pointer, its type and sender read by the getters
(`Message.GetType`/`GetFrom` on `msgIn`), and passed to `raft.Step` for good.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Step
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
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

set_option hygiene false in
/-- A message `RawNode.Step` does not step: load the error it returns and refold
`ownRawNode` unchanged. -/
local macro "early_return" e:term : tactic => `(tactic| (
  try wp_auto
  iapply HΦ $$ %$e %rs.term
  isplitl
  · iapply ownRawNode_intro γ rn id { rs with term := rs.term } s cf fp rnv sv hprev steps Hwf Hin
      Hal Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs
  ipureintro
  refine ⟨Int.le_refl _, by rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1, fun _ => ?_⟩
  split <;> omega))

set_option hygiene false in
/-- A premise of `raft.Step` about a type `RawNode.Step` does not take: vacuous. -/
local macro "not_net" : tactic => `(tactic| (intro h; first
  | (obtain h | h := h <;> (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty)))
  | (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty))))

/-- The two guards, each an early return or on (`all_goals` over the paths that go on),
then `raft.Step`. -/
theorem RawNode.Step.wp_proof
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    RawNode.Step.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs ml st Hok _Hdns Hmtc Htn Hpvb
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hok _Hdns Hmtc Htn Hpvb ⊢
  have Hok0 := Hok
  obtain ⟨Hty, -⟩ := Hok0
  have Hty0 : 0 ≤ sint.Z m.Type' := netStepTypes_nonneg Hty
  wp_start as H
  iNamed H
  iNamed Hrn
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto_lc 1
  -- `IsLocalMsg(m.Type) && !IsLocalMsgTarget(m.From)`
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  wp_apply wp_IsLocalMsg _ Hty0 as %b1 _
  wp_if_destruct
  all_goals try (wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
                 wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try early_return errStepLocal
  -- `IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) && trk.Progress[m.From] == nil`
  all_goals (wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
             wp_apply wp_IsResponseMsg _ Hty0 as %b2 _; wp_if_destruct)
  all_goals try (wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
                 wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try (
    icases ownRaftPhysC_tracker_same cf rnv.raft' id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    icases ownTrackerC_progress_map cf tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    try wp_auto
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ _ m.From' _
      $$ Hprs with -
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    wp_if_destruct)
  all_goals try early_return errStepPeer
  -- `rn.raft.Step(m)`
  all_goals (
      try wp_auto
      icases ownStepGhost_boot_term γ _ cf id s (m.Type' = MsgPreVote) Hpvb $$ Hghost
        with ⟨%Hb1, Hghost⟩
      have HnP : m.Type' ≠ MsgProp := by not_net
      icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
      wp_apply Hok.raftStep Hpvoff Htrm Hmtc Htn Hb1 (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp)
          Hwf
        (GMode.Pre.of_facts Hpf (by not_net) (by not_net))
        $$ [$Hphys $Hghost $Hlc1 Hm Hcred]
      · simp only [HnP, ↓reduceIte, named]
        isplitl [Hm]
        · isplitl [Hm]
          · iexact Hm
          isplitr
          · iempintro
          isplitr
          · ipureintro; not_net
          isplitr
          · ipureintro; not_net
          imodintro
          iintro %ty %Hty' _
          iapply Hmsg $$ %ty %Hty'
        isplitl [Hcred]
        · iexact Hcred
        imodintro
        iintro %h
        exfalso
        revert h
        not_net
      simp only [HnP]
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, %Hresp, -⟩
      have Hc := Href.commit_mono
      have e1 := Href.keep (by not_net) (by not_net); subst e1
      have e2 := Hcc (by not_net); subst c'
      obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by not_net) (by not_net)
      obtain ⟨Ht1, -, Ht3, -, Ht5, Hpcs⟩ := Htm (by not_net)
      have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
          (if m.Type' = MsgTimeoutNow then 1 else 0) := by
        intro hpr
        by_cases h : m.Type' = MsgTimeoutNow
        · rw [ite_eq_left h]; exact Ht5 h
        · rw [ite_eq_right h]; have := Ht3 (by not_net) hpr h; omega
      -- (2026-10-17) the term within the ceiling: the message's, a transfer's campaign's, or a
      -- pre-candidate's won pre-vote's
      have Hmtc' : uint.Z m.Term' ≤ uint.Z s.gh.tc := by rw [← Hpvoff.2.1]; exact Hmtc
      have Htc0 := Hpvoff.2.2.1
      have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
        by_cases hpr : m.Type' = MsgPreVoteResp
        · rcases (Hresp.2 hpr).1 with h | ⟨hp, h⟩
          · have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
          · have := Hpvoff.2.2.2 hp; omega
        · have h1 := Ht3' hpr
          by_cases h : m.Type' = MsgTimeoutNow
          · rw [ite_eq_left h] at h1
            have := Htn h; rw [Hpvoff.2.1, Htrm] at this; omega
          · rw [ite_eq_right h] at h1
            have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
      -- the queue survives any step, a truncating `MsgApp`'s too: what it needs of the log
      -- is `prev` and `stored`, which no network step changes (`NetFrame`)
      have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok
      ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
      wp_auto
      iapply HΦ $$ %err %s'.term
      isplitl
      · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf' Hin
          Hal
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          Hstok' rfl (by rw [Hsg]; exact Hstor)
          (Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net))
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩)

end proof

end EtcdGrove
end Perennial
