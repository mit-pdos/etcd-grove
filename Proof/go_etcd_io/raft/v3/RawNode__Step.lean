/- Lean-first (no Rocq counterpart).
raft v3.7 (2026-10-16, stage R5): the message is a pointer, its type and sender read by the getters
(`Message.GetType`/`GetFrom` on `msgIn`), and passed to `raft.Step` for good.

(2026-10-20, D22 S-c) A `MsgSnap` too: `raft.Step`'s snapshot clause (`SnapStep`, `SnapCfgOut`)
rebuilds the node at the configuration the restore installs (static: the ghost state's voters, not
joint, `GMode.SnapOk`), with the pending snapshot recorded in `RNState.psnap`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- A message `RawNode.Step` does not step: load the error it returns and refold
`ownRawNode` unchanged (but for the pending-snapshot flag the postcondition raises for a
`MsgSnap`, `Hps'`, `Hstrecs'`). -/
local macro "early_return" e:term : tactic => `(tactic| (
  try wp_auto
  iapply HΦ $$ %$e %rs.term
  isplitl
  · iapply ownRawNode_intro γ rn id
      { rs with term := rs.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s cf fp rnv sv
      hprev steps Hwf Hin Hal Hasync Hdlen Hunp
      (fun h => Hsnap ⟨Hps' h.1, h.2⟩) Hstok Htrm Hstor Hpvoff
      Hrs_out Hrs_unst Hrs_clb Hrnfl
      (Hloan.step rs.term rfl (fun _ => ⟨.inl rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩))
      Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc
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
then `raft.Step`; after it, a snapshot's step (`SnapStep`) or any other's (`NetFrame`). -/
theorem RawNode.Step.wp_proof
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    RawNode.Step.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs ml st Hok Hmtc Htn Hflw Hxt Hsnp
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hok Hmtc Htn Hxt Hsnp ⊢
  have Hok0 := Hok
  obtain ⟨Hty, -⟩ := Hok0
  have Hty0 : 0 ≤ sint.Z m.Type' := netStepTypes_nonneg Hty
  have Hps' : (rs.psnap || decide (m.Type' = MsgSnap)) = false → rs.psnap = false :=
    fun h => (Bool.or_eq_false_iff.1 h).1
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
      icases ownStepGhost_term0 γ _ cf id s $$ Hghost
        with ⟨%Hb1, Hghost⟩
      icases ownStepGhost_nsLink γ _ cf id s $$ Hghost with ⟨%Hnl, Hghost⟩
      have HnP : m.Type' ≠ MsgProp := by not_net
      icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
      -- (D22 S-d3b) the log and what the storage will hold, before the step (`ackInv`'s carry)
      icases ownRaftPhysC_persistRel cf rnv.raft' id s $$ Hphys with ⟨%Hpr, Hphys⟩
      icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh0, Hphys⟩
      have Hrel := fun h => Hpr.2 (ack_snap_sip Hloan Hgh0.1.2 h)
      -- (2026-10-28, stage U4a) `delivered`'s terms are the log's, for a restore's record
      icases ownRaftPhysC_applying cf rnv.raft' id s $$ Hphys with ⟨%Hac0, Hphys⟩
      icases ownStepGhost_dlv_terms γ _ cf id s rs.delivered
        (by have := uint_Z_nonneg s.logst.applying; rw [Hdlen]; omega) Hac0 $$ Hdeliv Hghost
        with ⟨%Hdag, Hghost⟩
      wp_apply Hok.raftStep Hpvoff Htrm Hmtc Htn Hb1 (Hrnfl.1 Hflw) (fun h => Hnl.2.1.trans (Hxt h)) (wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp)
          Hwf
        (RNMode.pre_net Hpf (by not_net)) (fun h => Hnl.1.trans (Hsnp h))
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
          · ipureintro; intro _; exact Hok.resps
          isplitr
          · ipureintro; not_net
          imodintro
          iintro %ty %Hty' %Hne
          iapply Hmsg $$ %ty %Hty' %Hne
        isplitl [Hcred]
        · iexact Hcred
        -- (2026-10-20, D22 S-c) a snapshot's facts, at the static mode
        imodintro
        iintro %h
        icases Hsnap $$ %h with ⟨%sv0, %scfg0, %Hp0, #Hm0, #Hd0, -⟩
        iexists sv0, scfg0
        iframe Hm0 Hd0
        ipureintro; exact Hp0
      simp only [HnP]
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, %Hresp, %Hsfr,
        %Htrc, -⟩
      have Hc := Href.commit_mono
      -- (2026-10-17) the term within the ceiling: the message's, a transfer's campaign's, or a
      -- pre-candidate's won pre-vote's
      have Hmtc' : uint.Z m.Term' ≤ uint.Z s.gh.tc := by rw [← Hpvoff.2.1]; exact Hmtc
      have Htc0 := Hpvoff.2.2.1
      by_cases Hs : m.Type' = MsgSnap
      · -- (2026-10-20, D22 S-c) a snapshot: the static mode, the restore's configuration; (D22
        -- S-d3b) any queue, the acknowledgement's facts carried across the restore (`ackInv_snap`)
        obtain ⟨⟨Ha, Hu, Hsd, Hsg, Hpre, Hgh, Hfl', Hap', Ht1, Ht2, Hpcs⟩, Hsl⟩ := Hsfr Hs
        -- (2026-10-28, stage U0) at the configuration it started at (until then the restore's)
        have e2 := Hcc (fun h => by rw [Hs] at h; simp [MsgSnap, MsgStorageAppendResp] at h); subst c'
        icases Hsnap $$ %Hs with ⟨%sv0, %scfg0, %Hp0, #Hm0, -, #Hloc0⟩
        obtain ⟨Hsn0, Hcl0, -⟩ := Hp0
        have Hsl0 := Hsl sv0 Hsn0
        -- (2026-10-26, D22 J2) the pending snapshot kept, or the message's, local to the node
        ihave #Hsloc' : snapLocOk γ id s'.logst.snap $$ []
        · rcases Hsl0 with ⟨-, h2, -, -⟩ | ⟨-, -, h2, -, -, -⟩
          · rw [h2]; iexact Hsloc
          · rw [h2]; iapply (snapLocOk_some γ id (snapId sv0)).2
            rw [show (snapId sv0).index' = sv0.Metadata'.Index' from rfl]; iexact Hloc0
        -- (2026-10-28, stage U3c) in either mode: the ghost part at a new full prefix (a restore's)
        obtain ⟨fp', ds', Hmd, Hfp'⟩ := RNMode.stepOut_snap Href Hs
        ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp', ds'⟩) cf id s' $$ [Hghost]
        · rw [← Hmd]; iexact Hghost
        have HnT : m.Type' ≠ MsgTimeoutNow := by rw [Hs]; simp [MsgSnap, MsgTimeoutNow]
        have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
            (if m.Type' = MsgTimeoutNow then 1 else 0) := by
          intro _; rw [ite_eq_right HnT]; omega
        have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
          have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
        ihave #HG2 := isMessage_snap_leadFull γ m sv0 scfg0 $$ [Hm0]
        · iapply isMessageC_isMessage γ _ $$ Hm0
        ihave #Hstr' : ackInv γ
            { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' $$ []
        · iapply ackInv_snap γ rfl Hstok Ht1 Hsd Hsl0 Hrel Hpr.1 $$ Hstrecs HG2
        -- (2026-10-28, stage U4a) the record of the storage's terms: kept, or the restore's of the
        -- log's terms, which are `delivered`'s
        have Hsdt' : SdtTie rs s' := Hsdt.snap Hdag Hsl0
        wp_auto
        iapply HΦ $$ %err %s'.term
        isplitl
        · iapply ownRawNode_intro γ rn id
              { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' cf fp'
              rnv sv hprev steps Hwf' Hin Hal
              Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
              (fun h => by have h1 := h.1; simp [Hs] at h1)
              (stepsOk_mono_st s s' _ Ht1 Hsd Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
              (by rw [Hsg]; exact Hstor)
              ((Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net)).fp_pc Hfp')
              (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
              (RNFl.keep Hrnfl Hfl' (by rw [Hap']; exact Int.le_refl _) Ha)
              (Hloan.step s'.term Hgh (fun _ => ⟨by
                  rcases Hsl0 with ⟨-, h2, -, -⟩ | ⟨-, -, h2, -, h3, -⟩
                  · exact .inl h2
                  · exact .inr ⟨_, h2, h3, by simp [Hs]⟩, Hfl', Hsd, Hu, Ha, Hc⟩))
              Hsdt' $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
        ipureintro
        rw [Htrm]
        exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩
      have e1 := Href.keep (by not_net) Hs (fun h => absurd h (by not_net)); subst e1
      have e2 := Hcc (fun h => absurd h (by not_net)); subst c'
      obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr Hs (by not_net) (fun h => absurd h (by not_net))
      obtain ⟨Ht1, -, Ht3, Hip4, Ht5, Hpcs⟩ := Htm Hs
      have Ht3' : m.Type' ≠ MsgPreVoteResp → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
          (if m.Type' = MsgTimeoutNow then 1 else 0) := by
        intro hpr
        by_cases h : m.Type' = MsgTimeoutNow
        · rw [ite_eq_left h]; exact Ht5 h
        · rw [ite_eq_right h]; have := Ht3 (by not_net) hpr h; omega
      have Hle : uint.Z s'.term ≤ uint.Z s.gh.tc := by
        by_cases hpr : m.Type' = MsgPreVoteResp
        · rcases (Hresp.2 hpr).1 with h | ⟨hp, h⟩
          · have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
          · have := Hpvoff.2.2.2.1 hp; omega
        · have h1 := Ht3' hpr
          by_cases h : m.Type' = MsgTimeoutNow
          · rw [ite_eq_left h] at h1
            have := Htn h; rw [Hpvoff.2.1, Htrm] at this; omega
          · rw [ite_eq_right h] at h1
            have := Int.max_le.2 ⟨Htc0, Hmtc'⟩; omega
      -- the queue survives any step, a truncating `MsgApp`'s too: what it needs of the log
      -- is `prev` and `stored`, which no network step changes (`NetFrame`)
      have Hstok' : StepsOk s' rs.steps :=
        stepsOk_mono_le s s' _ Ht1 ⟨Hpv, logStoreRec_stored Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok
      -- (D22 S-d3b) the acknowledgement's facts across the step: a `MsgApp`'s truncation, at an
      -- entry of its leader's log (`ackInv_app`), or `offsetInProgress` not moved back
      ihave #Hstr' : ackInv γ
          { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' $$ []
      · by_cases Happ : m.Type' = MsgApp
        · ihave #Hm' := Hmsg $$ %MsgType.app %(by rw [Happ]; exact mtypeOf_MsgApp) %(by decide)
          rw [isMessage_absMsg_ctx γ .app m ents ctx (And.intro (by decide) (by decide))]
          ihave #Hents := isMessage_app_leadFull γ m ents $$ Hm'
          iapply ackInv_app γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Htrc Happ) Hrel Hpr.1
            $$ Hstrecs Hents
        · iapply ackInv_keep γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 Happ) $$ Hstrecs
      ihave #Hsloc' : snapLocOk γ id s'.logst.snap $$ []
      · rw [Hsn]; iexact Hsloc
      wp_auto
      iapply HΦ $$ %err %s'.term
      isplitl
      · iapply ownRawNode_intro γ rn id
            { rs with term := s'.term, psnap := rs.psnap || decide (m.Type' = MsgSnap) } s' cf fp
            rnv sv hprev steps Hwf' Hin Hal
            Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp)
            (fun h => by rw [Hsn]; exact Hsnap ⟨Hps' h.1, h.2⟩)
            Hstok' rfl (by rw [Hsg]; exact Hstor)
            (Hpvoff.step rfl rfl Hpre Hgh Hle Hpcs (by not_net))
            (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
            (RNFl.keep Hrnfl Hfl' Hap' Ha)
            (Hloan.step s'.term Hgh (fun _ => ⟨.inl Hsn, Hfl', logStoreRec_stored Hsd, Hu, Ha, Hc⟩))
            (Hsdt.ofRec Hsn Hsd) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, by rw [Hpvoff.2.1]; exact Hle, Ht3'⟩)

end proof

end EtcdGrove
end Perennial
