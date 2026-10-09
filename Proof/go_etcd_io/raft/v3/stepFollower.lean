/-
Port of election_proof/proof_stepFollower.v.
-/
module

public import Spec.go_etcd_io.raft.v3.stepFollower
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Spec.go_etcd_io.raft.v3.raft__send

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option linter.unusedSimpArgs false in
/-- By type. The type switch's first test is against `MsgProp`
(`W32 2`); rewriting `m.Type` to its literal lets `wp_auto` decide
the rest by computation.

- `MsgVoteResp`, `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm
  matches; `return nil`.
- `MsgProp`, leaderless: `r.lead == None` holds, the `Infof` reads
  `r.id`, `r.Term` and the logger, and the `return` loads
  `ErrProposalDropped` -- a package global, whose points-to
  `isInitialized_access` hands out.
- `MsgProp`, with a leader: `disableProposalForwarding` is `false`
  (`raft.wp_load_disableProposalForwarding`), `m.To = r.lead` is a
  store into the local copy of `m`, and `send` takes clause (e).
- `MsgApp`/`MsgHeartbeat`/`MsgSnap`: two stores (`electionElapsed`,
  untracked, and `lead`), then `handleAppendEntries`/`handleHeartbeat`/
  `handleSnapshot` at `{ s with lead := m.From' }`. -/
theorem stepFollower.wp_proof
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    stepFollower.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents sv voters Hty Hprop Happ Hhb
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · -- `MsgVoteResp`: no arm
    rw [Hty]
    simp only [MsgVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgProp`
    obtain ⟨Hfrom0, Hterm0, Hlid⟩ := Hprop Hty
    rw [Hty]
    simp only [MsgProp]
    wp_auto
    wp_apply raft.wp_load_lead $$ Hphys as Hphys
    by_cases Hlead : s.lead = W64 0
    · -- leaderless: dropped
      rw [decide_eq_true Hlead]
      wp_auto
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_raft_log
      iapply HΦ $$ %errPropDropped %s %true
      iframe Hphys
      simp only [↓reduceIte]
      isplitr
      · ipureintro
        simp [FollowerStepResult, Hty, Hlead, MsgVoteResp, MsgProp]
      iexact ErrPropDropped
    · -- forwarded to the leader
      rw [decide_eq_false Hlead]
      wp_auto
      wp_apply raft.wp_load_disableProposalForwarding $$ Hphys as Hphys
      wp_apply raft.wp_load_lead $$ Hphys as Hphys
      ihave Hes := Hents $$ %(Or.inr trivial)
      icases Hes with ⟨#Hes, -⟩
      wp_apply wp_raft_send _ _ _ _ { m with To' := s.lead } ents [propForward id s.lead m ents]
          Hfrom0 (Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, Hterm0, fun h => Hlid h, rfl⟩))))
        $$ [$Hphys $Hes]
      · iapply send_no_snap
        simp [Hty, MsgProp, MsgSnap]
      iintro Hphys
      wp_auto
      iapply HΦ $$ %GoInterface.nil %_ %false
      iframe
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp]
      exact Hlead
  · -- `MsgApp`: adopt the sender as leader, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hnorm, Hconf⟩ := Happ Hty
    rw [Hty]
    simp only [MsgApp]
    wp_auto
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_store_lead $$ Hphys as Hphys
    ihave Hes := Hents $$ %(Or.inl trivial)
    icases Hes with ⟨#Hes, Hcap⟩
    wp_apply wp_raft_handleAppendEntries _ _ _ { s with lead := m.From' } _ _ Hwf Hnw Hnorm Hconf $$ [$Hphys $Hes $Hcap]
      as %s' ⟨Hphys, %Hres⟩
    iapply HΦ $$ %GoInterface.nil %s' %false
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    exact Hres
  · -- `MsgHeartbeat`: adopt the sender as leader, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    rw [Hty]
    simp only [MsgHeartbeat]
    wp_auto
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_store_lead $$ Hphys as Hphys
    wp_apply wp_raft_handleHeartbeat _ _ _ { s with lead := m.From' } _ Hcommit Hfrom $$ [$Hphys] as Hphys
    iapply HΦ $$ %GoInterface.nil %_ %false
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm
    rcases Hty with Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp] <;> wp_auto
    all_goals
      iapply HΦ $$ %GoInterface.nil %s %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      simp [FollowerStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
  · -- `MsgSnap`: adopt the sender as leader, then `handleSnapshot`
    ihave Hs := Hsnap $$ %Hty
    icases Hs with ⟨%Hsc, #Hsv, #Hvs⟩
    obtain ⟨Hscope, Hrole, Hvotes, Hcfg⟩ := Hsc
    rw [Hty]
    simp only [MsgSnap]
    wp_auto
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_store_lead $$ Hphys as Hphys
    wp_apply wp_raft_handleSnapshot _ _ _ { s with lead := m.From' } _ sv voters Hrole Hvotes Hcfg Hscope $$ [$Hphys $Hsv $Hvs]
      as %s' ⟨Hphys, %Hres⟩
    iapply HΦ $$ %GoInterface.nil %s' %false
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    exact Hres
  · -- `MsgPreVoteResp` (2026-10-04): no arm
    rw [Hty]
    simp only [MsgPreVoteResp]
    wp_auto
    iapply HΦ $$ %GoInterface.nil %s %false
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    simp [FollowerStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]

end proof

end EtcdGrove
end Perennial
