/-
Port of election_proof/proof_raft__switchToConfig.v; the leader case (2026-10-13,
reconfiguration stage D) and any configuration with a removed or demoted leader (2026-10-13,
stage A2) are Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.traceConfChangeEvent
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ConfState
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__IDs
public import Spec.go_etcd_io.raft.v3.raft__abortLeaderTransfer
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower

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

/-- `ownTrackerC` at two indices that are equal (by computation: a state reached by
record updates). -/
private theorem ownTracker_cast (c : CfgM) (tv : tracker.ProgressTracker) (t t' : Trk)
    (h : t = t') : ownTrackerC (GF := GF) c tv t ⊢ ownTrackerC c tv t' := h ▸ .rfl

/-- A learner of a configuration is no voter of it (`CfgInv`). -/
private theorem learner_not_voter (c : CfgM) (f : GMap w64 Bool) (H : CfgInv ⟨c, f⟩)
    (k : w64) (hl : k ∈ c.learners) : k ∉ c.voters := by
  obtain ⟨h1, h2, -⟩ := H.2.2.1 k hl
  intro hv
  unfold CfgM.voters at hv
  rcases (GMap.elem_of_union _ _ _).1 hv with h | h
  · exact h2 h
  · exact h1 h

/-- The body. After the install (`r.trk.Config = cfg; r.trk.Progress = trk`) the struct is at
`c` with `Hvoter` at `c.voters ∪ {[id]}` (the wand the caller hands in) until the role is
known to fit `c`: a leader that stays a voter, a candidate (a voter, by the premise) and a
follower are moved to `c.voters` (`ownRaftPhysCV_widen`); a removed or demoted leader steps
down first (`becomeFollower`, on the struct at `c.voters ∪ {[id]}`). -/
theorem raft.switchToConfig.wp_proof
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (wp_raft_maybeCommit : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG))
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG)) :
    raft.switchToConfig.spec (GF := GF) (hG := hG) := by
  intro c r id s tv0 cfgv prsm prs pvs Hlead Hcand
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_traceConfChangeEvent
  -- `r.trk.Config = cfg; r.trk.Progress = trk`: the one change of configuration
  icases typedPointsto_not_null_dup _ _ _ $$ Htrkf with ⟨Htrkf, %Hnn⟩
  iStructNamed Htrkf
  ihave Htrkf : r.[raft, go!"trk"] ↦
      ({ tv0 with Config' := cfgv, Progress' := prsm } : tracker.ProgressTracker)
      $$ [Votes MaxInflight MaxInflightBytes Config Progress]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Htrk := ownTrackerC_reconfig c tv0 s.votes cfgv prsm prs pvs Hmi $$ Hvotes Hnew
  ihave Hphys := Hback $$ %_ %prs %pvs Htrkf Htrk
  -- from here on the state is `s0`, and `s1` once `r.isLearner` is stored
  generalize Hs0 : ({ s with progress := prs, prvals := pvs } : NState) = s0
  have Hrole0 : s0.role = s.role := by rw [← Hs0]
  have Hprs0 : s0.progress = prs := by rw [← Hs0]
  have Hsdr0 : s0.sdr = s.sdr := by rw [← Hs0]
  -- the log line: `r.id`, `r.trk.Config`
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hback⟩
  wp_auto
  ihave Hphys := Hback $$ %tv1 Htrkf Htrk
  wp_raft_logC
  -- `cs := r.trk.ConfState()`
  icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_ConfState $$ [$Htrkf $Htrk]
    as %cs %xs %os %ls %lns ⟨Htrkf, Htrk, Hcs, Hos, Hls, Hlns, %Hcs0⟩
  ihave Hphys := Hback $$ %tv2 Htrkf Htrk
  -- `pr, ok := r.trk.Progress[r.id]`
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv3, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_progress_map c _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTrackerC_pure c _ _ $$ Htrk with ⟨%Hpure, Htrk⟩
  obtain ⟨Hinv, -, Hfl, -, -⟩ := Hpure
  simp only at Hdom Hinv Hfl
  wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  dsimp only
  -- `r.isLearner = ok && pr.IsLearner`: whether the node is a learner of `c`
  have HL : ∀ pr, s0.progress !! id = some pr → id ∉ c.voters → id ∈ c.learners := by
    intro pr hpr hv
    have hk : id ∈ c.ids := by rw [← Hdom, GMap.elem_of_dom]; exact ⟨pr, hpr⟩
    unfold CfgM.ids at hk
    rcases (GMap.elem_of_union _ _ _).1 hk with h | h
    · exact absurd h hv
    · exact h
  by_cases Hl : s.role = .leader
  · by_cases Hin : id ∈ c.voters
    · ------------------------------------------------------------------
      -- a leader that stays a voter
      obtain ⟨pr, Hlk⟩ : ∃ pr, s0.progress !! id = some pr := by
        rw [← GMap.elem_of_dom, Hdom]
        exact (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _ Hin
      rw [Hlk]
      simp only [Option.getD_some, Option.isSome_some]
      wp_auto
      icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
      iNamed Hpr
      have Hnl : id ∉ c.learners := fun h => learner_not_voter c _ Hinv id h Hin
      have Hnolearner : pv.IsLearner' = false := by
        rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
        exact decide_eq_false Hnl
      wp_auto
      rw [Hnolearner]
      ihave Htrk := Hprback $$ [Hpv Hinfl]
      · iapply ownProgress_intro $$ Hpv Hinfl
        ipureintro; exact Habs
      ihave Hphys := Hback $$ %tv3 Htrkf Htrk
      wp_apply raft.wp_store_isLearnerC $$ Hphys as Hphys
      have HLf : learnerOfC c id = false := decide_eq_false Hnl
      ihave Hphys := ownRaftPhysC_eq c r id _ { s0 with isLearner := learnerOfC c id }
        (by rw [HLf]) $$ Hphys
      -- the node fits `c`: `Hvoter` at `c.voters`
      ihave Hphys := ownRaftPhysCV_widen c c.voters r id _ (fun _ _ => Hin) $$ Hphys
      wp_apply raft.wp_load_isLearnerC $$ Hphys as Hphys
      generalize Hs1 : ({ s0 with isLearner := learnerOfC c id } : NState) = s1
      have Hs1l : s1.isLearner = false := by rw [← Hs1]; exact HLf
      rw [Hs1l]
      have Hrole1 : s1.role = s.role := by rw [← Hs1, ← Hs0]
      have Hl1 : s1.role = .leader := by rw [Hrole1]; exact Hl
      have Hst : stateW64 s1.role = W64 2 := by rw [Hl1]; rfl
      wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      rw [Hst]
      wp_auto
      ihave %Hxlen := ownSlice_len $$ Hcs
      -- `len(cs.Voters) == 0` (no incoming voter): nothing more
      wp_if_destruct
      · iapply HΦ $$ %cs %xs %os %ls %lns %s1
        iframe Hphys Hcs Hos Hls Hlns
        ipureintro
        refine ⟨Hcs0, ?_⟩
        have e : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c id } : NState)
            = s1 := by rw [← Hs1, ← Hs0]
        rw [e]
        unfold SwitchOkC
        rw [if_pos Hl1, if_pos Hin]
        exact ⟨s1.logst.committed, [], s1.prvals, s1.lt, .inl rfl, fun m hm => by simp at hm, rfl,
          by cases s1; simp [sendMsgs]⟩
      try wp_auto
      -- `if r.maybeCommit() { r.bcastAppend() } else { r.trk.Visit(...maybeSendAppend...) }`
      wp_apply wp_raft_maybeCommit c r id s1 Hl1 $$ [$Hphys] as %b %N ⟨Hphys, %HN⟩
      -- after the broadcast, the state is `s2` with sends `ms` and values `pvs2`
      wp_join iprop(∃ (ms : List Msg) (pvs2 : GMap w64 Progress),
          "Hphys" ∷ ownRaftPhysCV c c.voters r id
            { sendMsgs { s1 with logst := { s1.logst with committed :=
                if b then N else s1.logst.committed } } ms with prvals := pvs2 } ∗
          "%Hms" ∷ ⌜ReplSends id { s1 with logst := { s1.logst with committed :=
                if b then N else s1.logst.committed } } ms⌝ ∗
          "%Hmm" ∷ ⌜prvalsMatch pvs2 = prvalsMatch s1.prvals⌝ ∗
          "r" ∷ r_ptr ↦ r ∗ "cs" ∷ cs_ptr ↦ cs) at next
        with [Hphys r cs] as HR
      · cases b
        · -- no commit: probe every peer
          simp only [Bool.false_eq_true, ↓reduceIte]
          wp_auto
          have Hs1c : ({ s1 with logst := { s1.logst with committed := s1.logst.committed } } : NState)
              = s1 := by cases s1; rfl
          icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv, Htrkf, Htrk, Hrest⟩
          wp_apply wp_ProgressTracker_Visit c _ tv ⟨s1.votes, s1.progress, s1.prvals⟩ _
              (fun _ pvsx => iprop(∃ (ms : List Msg),
                "rp" ∷ r_ptr ↦ r ∗
                "%Hms" ∷ ⌜ReplSends id s1 ms⌝ ∗
                "%Hmm" ∷ ⌜prvalsMatch pvsx = prvalsMatch s1.prvals⌝ ∗
                "Hrest" ∷ (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
                    ownTrackerC c tvx ⟨s1.votes, s1.progress, pvsx'⟩ -∗
                    ownRaftPhysCV c c.voters r id { sendMsgs s1 ms with prvals := pvsx' })))
            $$ [$Htrkf $Htrk r Hrest]
          · isplitl [r Hrest]
            · iexists []
              simp only [named]
              iframe r
              isplitr
              · ipureintro; intro m Hm; simp at Hm
              isplitr
              · ipureintro; trivial
              iintro %tvx %pvsx Hf Ht
              ihave Hphys := Hrest $$ %tvx %pvsx Hf Ht
              iapply ownRaftPhysC_eq c r id _ _ (by cases s1; simp [sendMsgs]) $$ Hphys
            -- the closure
            imodintro
            unfold visitClosureC
            iintro %i %pr0 %tv0' %pvs0 %p0 %D
            wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback0, HI⟩
            iNamed HI
            ihave Htrk := Hback0 $$ %p0 Hpr %rfl
            ihave Hphys := Hrest $$ Htrkf Htrk
            wp_auto
            wp_apply raft.wp_load_idC $$ Hphys as Hphys
            by_cases Hii : i = id
            · -- the leader itself: nothing is sent
              rw [decide_eq_true Hii]
              wp_auto
              icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv1', Htrkf, Htrk, Hrest⟩
              ihave Htrk := ownTracker_cast c tv1' _ ⟨s1.votes, s1.progress, <[i := p0]> pvs0⟩ ?_
                $$ Htrk
              · rfl
              iapply HΦ
              iexists tv1', _
              iframe Htrkf Htrk
              iexists ms
              simp only [named]
              iframe rp
              isplitr
              · ipureintro; exact Hms
              isplitr
              · ipureintro; rw [GMap.insert_id _ _ _ Hpvi]; exact Hmm
              iintro %tvx %pvsx Hf Ht
              ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
              · iapply ownTracker_cast c tvx ⟨s1.votes, s1.progress, pvsx⟩ _ ?_ $$ Ht
                rfl
              iapply ownRaftPhysC_eq c r id _ _ (by cases s1; rfl) $$ Hphys
            · -- a peer: `maybeSendAppend(id, false)`
              rw [decide_eq_false Hii]
              wp_auto
              wp_apply wp_raft_maybeSendAppend _ _ _ _ i false Hii (by exact Hicfg) $$ [$Hphys]
                as %b' %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
              try wp_auto
              icases ownRaftPhysC_tracker_prvals $$ Hphys with ⟨%tv1', Htrkf, Htrk, Hrest⟩
              ihave Htrk := ownTracker_cast c tv1' _ ⟨s1.votes, s1.progress, pvs'⟩ ?_ $$ Htrk
              · rfl
              iapply HΦ
              iexists tv1', _
              iframe Htrkf Htrk
              iexists ms ++ ms'
              simp only [named]
              iframe rp
              isplitr
              · ipureintro
                exact replSends_app id s1 ms ms' Hms ((replSends_send_prvals id s1 ms _ ms').1 Hms')
              isplitr
              · ipureintro; simp only at Hmm'; rw [Hmm', GMap.insert_id _ _ _ Hpvi]; exact Hmm
              iintro %tvx %pvsx Hf Ht
              ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
              · iapply ownTracker_cast c tvx ⟨s1.votes, s1.progress, pvsx⟩ _ ?_ $$ Ht
                rfl
              iapply ownRaftPhysC_eq c r id _ _
                (by cases s1; simp [sendMsgs, List.append_assoc]) $$ Hphys
          iintro ⟨%tvfin, %pvsfin, Htrkf, Htrk, HI⟩
          iNamed HI
          ihave Hphys := Hrest $$ %tvfin %pvsfin Htrkf Htrk
          wp_auto
          wp_join_done
          iexists ms, pvsfin
          simp only [Hs1c]
          iframe
          ipureintro
          exact ⟨Hms, Hmm⟩
        · -- a commit: broadcast
          simp only [↓reduceIte]
          wp_auto
          wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs2 ⟨Hphys, %Hms, %Hmm⟩
          wp_join_done
          iexists ms, pvs2
          simp only
          iframe
          ipureintro
          exact ⟨Hms, Hmm⟩
      iNamed HR
      -- the final state, before the transfer check
      generalize Hs3 : ({ sendMsgs { s1 with logst := { s1.logst with committed :=
          if b then N else s1.logst.committed } } ms with prvals := pvs2 } : NState) = s3
      -- `if _, tOK := r.trk.Config.Voters.IDs()[r.leadTransferee]; !tOK && r.leadTransferee != 0`
      wp_auto
      wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
      icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv4, Htrkf, Htrk, Hback⟩
      try wp_auto
      wp_apply (quorum.JointConfig.IDs.spec_trackerC wp_JointConfig_IDs) $$ [$Htrkf $Htrk]
        as %mref ⟨Htrkf, Htrk, Hidm⟩
      ihave Hphys := Hback $$ %tv4 Htrkf Htrk
      wp_apply wp_map_lookup2 $$ Hidm as -
      try dsimp only
      have Hc : (if b then N else s1.logst.committed) = s1.logst.committed ∨
          CommitOkC c (toPState s1) (if b then N else s1.logst.committed) := by
        cases b
        · left; rfl
        · right; exact HN rfl
      have Hres : ∀ lt', LeaderSwitchC c id s1 { s3 with lt := lt' } := by
        intro lt'
        refine ⟨_, ms, pvs2, lt', Hc, Hms, Hmm, ?_⟩
        rw [← Hs3]
      wp_join iprop(∃ (s' : NState),
          "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗ "%Hs'" ∷ ⌜LeaderSwitchC c id s1 s'⌝ ∗
          "r" ∷ r_ptr ↦ r ∗ "cs" ∷ cs_ptr ↦ cs) at next
        with [Hphys r cs] as HR2
      · have Hkeep : LeaderSwitchC c id s1 s3 := by
          have := Hres s3.lt
          rwa [show ({ s3 with lt := s3.lt } : NState) = s3 by cases s3; rfl] at this
        wp_if_destruct
        all_goals first
          | (wp_join_done
             iexists s3
             iframe
             ipureintro; exact Hkeep)
          | (wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
             wp_if_destruct
             all_goals first
               | (wp_apply wp_raft_abortLeaderTransfer $$ [$Hphys] as Hphys
                  wp_join_done
                  iexists _
                  iframe
                  ipureintro; exact Hres _)
               | (wp_join_done
                  iexists s3
                  iframe
                  ipureintro; exact Hkeep))
      iNamed HR2
      wp_auto
      iapply HΦ $$ %cs %xs %os %ls %lns %s'
      iframe Hphys Hcs Hos Hls Hlns
      ipureintro
      subst Hs0 Hs1
      refine ⟨Hcs0, ?_⟩
      unfold SwitchOkC
      rw [if_pos Hl1, if_pos Hin]
      exact Hs'
    · ------------------------------------------------------------------
      -- a leader removed or demoted: it steps down (`stepDownOnRemoval`, by the premise)
      have Hsdr : s.sdr = true := by
        rcases Hlead Hl with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h Hin
        · exact h
      have Hst : stateW64 s0.role = W64 2 := by rw [Hrole0, Hl]; rfl
      -- `r.isLearner = ok && pr.IsLearner`, then `(!ok || r.isLearner) && r.state == Leader`
      cases Hlk : s0.progress !! id with
      | some pr =>
        simp only [Option.getD_some, Option.isSome_some]
        try wp_auto
        icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
        iNamed Hpr
        have Hlr : id ∈ c.learners := HL pr Hlk Hin
        have Hlearner : pv.IsLearner' = true := by
          rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
          exact decide_eq_true Hlr
        try wp_auto
        rw [Hlearner]
        ihave Htrk := Hprback $$ [Hpv Hinfl]
        · iapply ownProgress_intro $$ Hpv Hinfl
          ipureintro; exact Habs
        ihave Hphys := Hback $$ %tv3 Htrkf Htrk
        wp_apply raft.wp_store_isLearnerC $$ Hphys as Hphys
        try wp_auto
        wp_apply raft.wp_load_isLearnerC $$ Hphys as Hphys
        try dsimp only
        try wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try dsimp only
        rw [Hst]
        try wp_auto
        have HLL : learnerOfC c id = true := decide_eq_true Hlr
        generalize Hs1 : ({ s0 with isLearner := true } : NState) = s1
        have Hsdr1 : s1.sdr = true := by rw [← Hs1]; exact Hsdr0.trans Hsdr
        have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hrole0.trans Hl
        wp_apply raft.wp_load_stepDownOnRemovalC $$ Hphys as Hphys
        rw [Hsdr1]
        try wp_auto
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        wp_apply wp_raft_becomeFollower c r id _ _ (W64 0) (Int.le_refl _) $$ [$Hphys]
          as %pvs' Hphys
        ihave Hphys := ownRaftPhysCV_widen c c.voters r id _
          (fun _ h => absurd (show PRole.follower = PRole.follower from rfl) h) $$ Hphys
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %_
        iframe Hphys Hcs Hos Hls Hlns
        ipureintro
        refine ⟨Hcs0, ?_⟩
        have e : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c id } : NState)
            = s1 := by rw [← Hs1, ← Hs0, HLL]
        rw [e]
        unfold SwitchOkC
        rw [if_pos Hl1, if_neg Hin]
        exact ⟨pvs', rfl⟩
      | none =>
        simp only [Option.getD_none, Option.isSome_none]
        try wp_auto
        ihave Hphys := Hback $$ %tv3 Htrkf Htrk
        wp_apply raft.wp_store_isLearnerC $$ Hphys as Hphys
        try wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try dsimp only
        rw [Hst]
        try wp_auto
        have HLL : learnerOfC c id = false := by
          unfold learnerOfC
          apply decide_eq_false
          intro h
          have hk : id ∈ domSet s0.progress := by
            rw [Hdom]; exact (GMap.elem_of_subseteq _ _).1 (learners_sub_ids c) _ h
          rw [GMap.elem_of_dom] at hk
          obtain ⟨x, hx⟩ := hk
          rw [Hlk] at hx; cases hx
        generalize Hs1 : ({ s0 with isLearner := false } : NState) = s1
        have Hsdr1 : s1.sdr = true := by rw [← Hs1]; exact Hsdr0.trans Hsdr
        have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hrole0.trans Hl
        wp_apply raft.wp_load_stepDownOnRemovalC $$ Hphys as Hphys
        rw [Hsdr1]
        try wp_auto
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        wp_apply wp_raft_becomeFollower c r id _ _ (W64 0) (Int.le_refl _) $$ [$Hphys]
          as %pvs' Hphys
        ihave Hphys := ownRaftPhysCV_widen c c.voters r id _
          (fun _ h => absurd (show PRole.follower = PRole.follower from rfl) h) $$ Hphys
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %_
        iframe Hphys Hcs Hos Hls Hlns
        ipureintro
        refine ⟨Hcs0, ?_⟩
        have e : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c id } : NState)
            = s1 := by rw [← Hs1, ← Hs0, HLL]
        rw [e]
        unfold SwitchOkC
        rw [if_pos Hl1, if_neg Hin]
        exact ⟨pvs', rfl⟩
  · ------------------------------------------------------------------
    -- a non-leader: done. It fits `c`: a candidate is a voter by the premise.
    have Hfit : s.role ≠ .follower → id ∈ c.voters := by
      intro hf
      apply Hcand
      cases h : s.role
      · exact absurd h hf
      · exact .inl rfl
      · exact absurd h Hl
      · exact .inr rfl
    have Hns : stateW64 s0.role ≠ W64 2 := by
      rw [Hrole0]
      cases h : s.role <;> simp_all [stateW64, StateFollower, StateCandidate, StatePreCandidate]
    have HSw : SwitchOkC c id { s0 with isLearner := learnerOfC c id }
        { s0 with isLearner := learnerOfC c id } := by
      unfold SwitchOkC; rw [if_neg (by show s0.role ≠ _; rw [Hrole0]; exact Hl)]
    ihave Hphys := Hback $$ %tv3 Htrkf Htrk
    ihave Hphys := ownRaftPhysCV_widen c c.voters r id _
      (fun _ h => Hfit (by rw [← Hrole0]; exact h)) $$ Hphys
    icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv3', Htrkf, Htrk, Hback⟩
    cases Hlk : s0.progress !! id with
    | some pr =>
      simp only [Option.getD_some, Option.isSome_some]
      wp_auto
      icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
      iNamed Hpr
      have Hnolearner : pv.IsLearner' = learnerOfC c id := by
        rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
        rfl
      wp_auto
      rw [Hnolearner]
      ihave Htrk := Hprback $$ [Hpv Hinfl]
      · iapply ownProgress_intro $$ Hpv Hinfl
        ipureintro; exact Habs
      ihave Hphys := Hback $$ %tv3' Htrkf Htrk
      wp_apply raft.wp_store_isLearnerC $$ Hphys as Hphys
      wp_apply raft.wp_load_isLearnerC $$ Hphys as Hphys
      try dsimp only
      cases HL' : learnerOfC c id
      · wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try dsimp only
        rw [decide_eq_false Hns]
        wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %_
        rw [HL'] at HSw
        iframe
        ipureintro
        subst Hs0
        exact ⟨Hcs0, HSw⟩
      · wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try dsimp only
        rw [decide_eq_false Hns]
        wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try dsimp only
        rw [decide_eq_false Hns]
        wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %_
        rw [HL'] at HSw
        iframe
        ipureintro
        subst Hs0
        exact ⟨Hcs0, HSw⟩
    | none =>
      simp only [Option.getD_none, Option.isSome_none]
      wp_auto
      ihave Hphys := Hback $$ %tv3' Htrkf Htrk
      wp_apply raft.wp_store_isLearnerC $$ Hphys as Hphys
      have HLf : learnerOfC c id = false := by
        unfold learnerOfC
        apply decide_eq_false
        intro h
        have hk : id ∈ domSet s0.progress := by
          rw [Hdom]; exact (GMap.elem_of_subseteq _ _).1 (learners_sub_ids c) _ h
        rw [GMap.elem_of_dom] at hk
        obtain ⟨x, hx⟩ := hk
        rw [Hlk] at hx; cases hx
      rw [HLf] at HSw
      -- `!ok` is `true`: the `||` does not load `r.isLearner`, and `r.state` is loaded by
      -- both `if`s
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      try dsimp only
      rw [decide_eq_false Hns]
      wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      try dsimp only
      rw [decide_eq_false Hns]
      wp_auto
      iapply HΦ $$ %cs %xs %os %ls %lns %_
      iframe
      ipureintro
      subst Hs0
      refine ⟨Hcs0, ?_⟩
      rw [HLf]
      exact HSw

end proof

end EtcdGrove
end Perennial
