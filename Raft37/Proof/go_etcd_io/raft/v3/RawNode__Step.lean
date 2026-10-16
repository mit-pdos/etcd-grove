/- Lean-first (no Rocq counterpart). 
raft v3.7 (2026-10-16, stage R5): the message is a pointer, its type and sender read by the getters
(`Message.GetType`/`GetFrom` on `msgIn`), and passed to `raft.Step` for good.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.RawNode__Step
public import Raft37.Spec.go_etcd_io.raft.v3.raft__Step
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Raft37.Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Raft37.Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Raft37.Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
-- `Step.commit_mono`
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.Facts

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
  ipureintro; refine ⟨Int.le_refl _, ?_⟩; split <;> omega))

set_option hygiene false in
/-- A premise of `raft.Step` about a type `RawNode.Step` does not take: vacuous. -/
local macro "not_net" : tactic => `(tactic| (intro h; first | exact h.elim |
  (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty)))

/-- A stamped type is not one of the unstamped ones. -/
local macro "ty_ne" : tactic => `(tactic| (simp [UnstampedType, MsgApp, MsgAppResp, MsgVote,
  MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp,
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader]))

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
  intro γ rn id rs ml st Hok _Hdns Htn
  rcases st with ⟨m, ents, sn, ctx, rsp⟩
  simp only at Hok _Hdns Htn ⊢
  have Hok0 := Hok
  obtain ⟨Hty, Hnri, Hri, Hself, Hrej, -⟩ := Hok0
  have Hnr : ∀ {t : w32}, m.Type' = t → ¬ UnstampedType t →
      m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 :=
    fun h ht => Hnri (h ▸ ht)
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
      have HnP : m.Type' ≠ MsgProp := by not_net
      have Hsm : StepMsg m := netStepTypes_stepMsg Hty
      have Hrest : RestMsgOk s m ents ctx := Hok.restMsgOk (by rw [← Htrm]; exact Htn)
      have P1 : m.Type' = MsgHup → m.Term' = W64 0 ∧ uint.Z s.term + 1 < 2 ^ 64 := by not_net
      have P2 : m.Type' = MsgPreVote → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
          m.From' ≠ id ∧ (s.term = W64 0 → plogUpToDate s.logst.prev
            (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index') = true) ∧
          s.prevote = true := by
        not_net
      have P3 : m.Type' = MsgPreVoteResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
          (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) := by not_net
      have P4 : m.Type' = MsgSnap → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
          m.From' ≠ id := by not_net
      have P5 : m.Type' = MsgBeat → m.Term' = W64 0 := by not_net
      have P6 : m.Type' = MsgProp → m.Term' = W64 0 ∧ (m.From' = W64 0 ∨ m.From' = id) := by
        not_net
      have P7 : m.Type' = MsgStorageAppendResp → sn = none ∧
          uint.Z m.Term' ≤ uint.Z s.term ∧
          (m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
            StableOk s.logst (entryID.mk m.LogTerm' m.Index')) ∧ s.gh.unst = false := by
        not_net
      have P8 : m.Type' = MsgStorageApplyResp → m.Term' = W64 0 := by not_net
      icases ownRaftPhysC_preFacts cf rnv.raft' id s Hpvoff $$ Hphys with ⟨%Hpf, Hphys⟩
      wp_apply wp_raft_Step cf _ γ _ id s ml m ents ctx sn rsp Hsm P1
        (fun h => Hnr h (by ty_ne))
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1⟩) P2 P3
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
          Hself (.inl h)⟩)
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
          Hself (.inr (.inl h))⟩)
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
          Hrej h⟩)
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
          Hself (.inr (.inr (.inl h)))⟩)
        P4 P5 P6 P7 P8
        (fun h => Hri (.inl h))
        (by not_net)
        (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
          Hself (.inr (.inr (.inr h)))⟩) Hrest Hwf
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
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, -, -⟩
      have Hc := Href.commit_mono
      have e1 := Href.keep (by not_net) (by not_net); subst e1
      have e2 := Hcc (by not_net); subst c'
      obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by not_net) (by not_net)
      obtain ⟨Ht1, -, Ht3, -, Ht5⟩ := Htm (by not_net)
      have Ht3 : uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') +
          (if m.Type' = MsgTimeoutNow then 1 else 0) := by
        by_cases h : m.Type' = MsgTimeoutNow
        · rw [ite_eq_left h]; exact Ht5 h
        · rw [ite_eq_right h]; have := Ht3 (by not_net) (by not_net) h; omega
      -- the queue survives any step, a truncating `MsgApp`'s too: what it needs of the log
      -- is `prev` and `stored`, which no network step changes (`NetFrame`)
      have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok
      ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
      wp_auto
      iapply HΦ $$ %err %s'.term
      isplitl
      · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf' Hin
          Hal
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          Hstok' rfl (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, Ht3⟩)

end proof

end EtcdGrove
end Perennial
