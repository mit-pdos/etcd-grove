/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Step
public import Spec.go_etcd_io.raft.v3.raft__Step
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
  · iapply ownRawNode_intro γ rn id { rs with term := rs.term } s ps rnv sv steps Hrel Hin
      Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs
  ipureintro; constructor <;> omega))

set_option hygiene false in
/-- A premise of `raft.Step` about a type `RawNode.Step` does not take: vacuous. -/
local macro "not_net" : tactic => `(tactic| (intro h; first | exact h.elim |
  (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp] at Hty)))

/-- The two guards, each an early return or on (`all_goals` over the paths that go on),
then `raft.Step`. -/
theorem RawNode.Step.wp_proof
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Step.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs m ents ctx Hok
  obtain ⟨Hty, Hto, Hterm, Hfrom, Hself, Hrej⟩ := Hok
  have Hty0 : 0 ≤ sint.Z m.Type' := by
    simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hty
    rcases Hty with h | h | h | h | h | h <;> rw [h] <;> decide
  wp_start as H
  iNamed H
  iNamed Hrn
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto
  -- `IsLocalMsg(m.Type) && !IsLocalMsgTarget(m.From)`
  wp_apply wp_IsLocalMsg _ Hty0 as %b1 _
  wp_if_destruct
  all_goals try (wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try early_return errStepLocal
  -- `IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) && trk.Progress[m.From] == nil`
  all_goals (wp_apply wp_IsResponseMsg _ Hty0 as %b2 _; wp_if_destruct)
  all_goals try (wp_apply wp_IsLocalMsgTarget m.From'; wp_if_destruct)
  all_goals try (
    icases ownRaftPhys_tracker_same γ.reCfg rnv.raft' id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    icases ownTracker_progress_map γ.reCfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    wp_auto
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ _ m.From' _
      $$ Hprs with -
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    wp_if_destruct)
  all_goals try early_return errStepPeer
  -- `rn.raft.Step(m)`
  all_goals (
      try wp_auto
      have HnP : m.Type' ≠ MsgProp := by not_net
      have Hsm : StepMsg m := by
        simp only [StepMsg, stepMsgTypes]
        simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hty
        rcases Hty with h | h | h | h | h | h <;> simp [h]
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
      have P7 : m.Type' = MsgStorageAppendResp → m.Snapshot' = null ∧
          uint.Z m.Term' ≤ uint.Z s.term ∧
          (m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
            StableOk s.logst (entryID.mk m.LogTerm' m.Index')) ∧ s.gh.unst = false := by
        not_net
      have P8 : m.Type' = MsgStorageApplyResp → m.Term' = W64 0 := by not_net
      wp_apply wp_raft_Step γ.reCfg γ _ id s ps m ents rfl Hsm Hin P1
        (fun _ => ⟨Hto, Hterm, Hfrom⟩) (fun _ => ⟨Hto, Hterm⟩) P2 P3
        (fun h => ⟨Hto, Hterm, Hfrom, Hself (.inl h)⟩)
        (fun h => ⟨Hto, Hterm, Hfrom, Hself (.inr (.inl h))⟩)
        (fun h => ⟨Hto, Hterm, Hfrom, Hrej h⟩)
        (fun h => ⟨Hto, Hterm, Hfrom, Hself (.inr (.inr h))⟩)
        P4 P5 P6 P7 P8 Hrel
        $$ [$Hphys $Hghost Hents_cap]
      · simp only [HnP, ↓reduceIte, named]
        isplitl [Hents_cap]
        · isplitr
          · iexact Hents
          isplitl [Hents_cap]
          · iexact Hents_cap
          isplitr
          · ipureintro; not_net
          isplitr
          · ipureintro; not_net
          imodintro
          iintro %ty %Hty' _
          iapply Hmsg $$ %ty %Hty'
        isplitr
        · iexists ctx
          iframe Hctx
          ipureintro; exact Hctx_ok
        imodintro
        iintro %h
        exfalso
        revert h
        not_net
      simp only [HnP, ↓reduceIte]
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, -, -⟩
      obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩ := Hfr (by not_net) (by not_net)
      obtain ⟨Ht1, -, Ht3, -⟩ := Htm (by not_net)
      have Ht3 := Ht3 (by not_net) (by not_net)
      have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
        obtain ⟨recv, Hst⟩ := Href
        have H := Step.commit_mono Hst
        rw [← Hrel.1, ← Hrel'.1] at H
        exact H
      -- the queue survives any step, a truncating `MsgApp`'s too: what it needs of the log
      -- is `prev` and `stored`, which no network step changes (`NetFrame`)
      have Hstok' : StepsOk s' rs.steps := stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok
      ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
      wp_auto
      iapply HΦ $$ %err %s'.term
      isplitl
      · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' ps' rnv sv steps Hrel' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          Hstok' rfl (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, Ht3⟩)

end proof

end EtcdGrove
end Perennial
