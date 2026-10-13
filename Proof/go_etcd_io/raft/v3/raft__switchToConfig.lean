/-
Port of election_proof/proof_raft__switchToConfig.v; the leader case (2026-10-13,
reconfiguration stage D) is Lean-first.
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

/-- `ownTracker` at two indices that are equal (by computation: a state reached by
record updates). -/
private theorem ownTracker_cast (cfg : GSet w64) (tv : tracker.ProgressTracker) (t t' : Trk)
    (h : t = t') : ownTracker (GF := GF) cfg tv t ⊢ ownTracker cfg tv t' := h ▸ .rfl

theorem raft.switchToConfig.wp_proof
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (wp_raft_maybeCommit : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG))
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG)) :
    raft.switchToConfig.spec (GF := GF) (hG := hG) := by
  intro cfg r id s tv0 cfgv prsm prs pvs Hlead
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
  ihave Htrk := ownTracker_reconfigV cfg tv0 s.votes cfgv prsm prs pvs Hmi $$ Hvotes Hnew
  ihave Hphys := Hback $$ %_ %prs %pvs Htrkf Htrk
  -- from here on the state is `s1`
  generalize Hs1 : ({ s with progress := prs, prvals := pvs } : NState) = s1
  have Hrole1 : s1.role = s.role := by rw [← Hs1]
  have Hprs1 : s1.progress = prs := by rw [← Hs1]
  -- the log line: `r.id`, `r.trk.Config`
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hback⟩
  wp_auto
  ihave Hphys := Hback $$ %tv1 Htrkf Htrk
  wp_raft_log
  -- `cs := r.trk.ConfState()`
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_ConfState $$ [$Htrkf $Htrk]
    as %cs %xs ⟨Htrkf, Htrk, Hcs, %Hxs, %Hcs0⟩
  ihave Hphys := Hback $$ %tv2 Htrkf Htrk
  -- `pr, ok := r.trk.Progress[r.id]`
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv3, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  dsimp only
  by_cases Hl : s.role = .leader
  · ------------------------------------------------------------------
    -- a leader that stays a voter
    obtain ⟨Hin, -⟩ := Hlead Hl
    have Hl1 : s1.role = .leader := by rw [Hrole1]; exact Hl
    have Hst : stateW64 s1.role = W64 2 := by rw [Hl1]; rfl
    obtain ⟨pr, Hlk⟩ : ∃ pr, s1.progress !! id = some pr := by
      rw [← GMap.elem_of_dom, Hdom]; exact Hin
    rw [Hlk]
    simp only [Option.getD_some, Option.isSome_some]
    wp_auto
    icases ownTracker_lookup_same cfg _ _ id pr Hlk $$ Htrk with ⟨%p, -, Hpr, Hprback⟩
    iNamed Hpr
    have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
    wp_auto
    rw [Hnolearner]
    ihave Htrk := Hprback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    ihave Hphys := Hback $$ %tv3 Htrkf Htrk
    wp_apply raft.wp_store_isLearner $$ Hphys as Hphys
    wp_apply raft.wp_load_isLearner $$ Hphys as Hphys
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    rw [Hst]
    ihave %Hxlen := ownSlice_len $$ Hcs
    have Hxne : xs.length ≠ 0 := by
      intro h
      have : id ∈ xs := Hxs.mem_iff.2 ((GMap.elem_of_elements cfg id).2 Hin)
      rw [List.length_eq_zero_iff] at h; rw [h] at this; simp at this
    wp_auto
    rw [decide_eq_false (show ¬ (cs.Voters'.len = W64 0) by
      intro h; apply Hxne
      rw [Hxlen.1, h]; rfl)]
    wp_auto
    -- `if r.maybeCommit() { r.bcastAppend() } else { r.trk.Visit(...maybeSendAppend...) }`
    wp_apply wp_raft_maybeCommit cfg r id s1 Hl1 Hin $$ [$Hphys] as %b %N ⟨Hphys, %HN⟩
    -- after the broadcast, the state is `s2` with sends `ms` and values `pvs2`
    wp_join iprop(∃ (ms : List Msg) (pvs2 : GMap w64 Progress),
        "Hphys" ∷ ownRaftPhys cfg r id
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
        icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv, Htrkf, Htrk, Hrest⟩
        wp_apply wp_ProgressTracker_Visit cfg _ tv ⟨s1.votes, s1.progress, s1.prvals⟩ _
            (fun _ pvsx => iprop(∃ (ms : List Msg),
              "rp" ∷ r_ptr ↦ r ∗
              "%Hms" ∷ ⌜ReplSends id s1 ms⌝ ∗
              "%Hmm" ∷ ⌜prvalsMatch pvsx = prvalsMatch s1.prvals⌝ ∗
              "Hrest" ∷ (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
                  ownTracker cfg tvx ⟨s1.votes, s1.progress, pvsx'⟩ -∗
                  ownRaftPhys cfg r id { sendMsgs s1 ms with prvals := pvsx' })))
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
            iapply ownRaftPhys_eq cfg r id _ _ (by cases s1; simp [sendMsgs]) $$ Hphys
          -- the closure
          imodintro
          unfold visitClosure
          iintro %i %pr0 %tv0' %pvs0 %p0 %D
          wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback0, HI⟩
          iNamed HI
          ihave Htrk := Hback0 $$ Hpr
          ihave Hphys := Hrest $$ Htrkf Htrk
          wp_auto
          wp_apply raft.wp_load_id $$ Hphys as Hphys
          by_cases Hii : i = id
          · -- the leader itself: nothing is sent
            rw [decide_eq_true Hii]
            wp_auto
            icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1', Htrkf, Htrk, Hrest⟩
            ihave Htrk := ownTracker_cast cfg tv1' _ ⟨s1.votes, s1.progress, <[i := p0]> pvs0⟩ ?_
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
            · iapply ownTracker_cast cfg tvx ⟨s1.votes, s1.progress, pvsx⟩ _ ?_ $$ Ht
              rfl
            iapply ownRaftPhys_eq cfg r id _ _ (by cases s1; rfl) $$ Hphys
          · -- a peer: `maybeSendAppend(id, false)`
            rw [decide_eq_false Hii]
            wp_auto
            wp_apply wp_raft_maybeSendAppend _ _ _ _ i false Hii Hicfg $$ [$Hphys]
              as %b' %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
            try wp_auto
            icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1', Htrkf, Htrk, Hrest⟩
            ihave Htrk := ownTracker_cast cfg tv1' _ ⟨s1.votes, s1.progress, pvs'⟩ ?_ $$ Htrk
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
            · iapply ownTracker_cast cfg tvx ⟨s1.votes, s1.progress, pvsx⟩ _ ?_ $$ Ht
              rfl
            iapply ownRaftPhys_eq cfg r id _ _
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
    wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
    icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv4, Htrkf, Htrk, Hback⟩
    try wp_auto
    wp_apply (quorum.JointConfig.IDs.spec_tracker wp_JointConfig_IDs) $$ [$Htrkf $Htrk]
      as %mref %idm ⟨Htrkf, Htrk, Hidm, %Hdomidm⟩
    ihave Hphys := Hback $$ %tv4 Htrkf Htrk
    wp_apply wp_map_lookup2 $$ Hidm as -
    try dsimp only
    have Hc : (if b then N else s1.logst.committed) = s1.logst.committed ∨
        CommitOk cfg (toPState s1) (if b then N else s1.logst.committed) := by
      cases b
      · left; rfl
      · right; exact HN rfl
    have Hres : ∀ lt', LeaderSwitch cfg id s1 { s3 with lt := lt' } := by
      intro lt'
      refine ⟨_, ms, pvs2, lt', Hc, Hms, Hmm, ?_⟩
      rw [← Hs3]
    wp_join iprop(∃ (s' : NState),
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗ "%Hs'" ∷ ⌜LeaderSwitch cfg id s1 s'⌝ ∗
        "r" ∷ r_ptr ↦ r ∗ "cs" ∷ cs_ptr ↦ cs) at next
      with [Hphys r cs] as HR2
    · have Hkeep : LeaderSwitch cfg id s1 s3 := by
        have := Hres s3.lt
        rwa [show ({ s3 with lt := s3.lt } : NState) = s3 by cases s3; rfl] at this
      wp_if_destruct
      all_goals first
        | (wp_join_done
           iexists s3
           iframe
           ipureintro; exact Hkeep)
        | (wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys
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
    iapply HΦ $$ %cs %xs %s'
    iframe Hphys Hcs
    ipureintro
    refine ⟨Hxs, Hcs0, ?_⟩
    unfold SwitchOk
    rw [if_pos Hl1]
    exact Hs'
  · ------------------------------------------------------------------
    -- a non-leader: done
    have Hns : stateW64 s1.role ≠ W64 2 := by
      rw [Hrole1]
      cases h : s.role <;> simp_all [stateW64, StateFollower, StateCandidate, StatePreCandidate]
    have HSw : SwitchOk cfg id s1 s1 := by
      unfold SwitchOk; rw [if_neg (by rw [Hrole1]; exact Hl)]
    cases Hlk : s1.progress !! id with
    | some pr =>
      simp only [Option.getD_some, Option.isSome_some]
      wp_auto
      icases ownTracker_lookup_same cfg _ _ id pr Hlk $$ Htrk with ⟨%p, -, Hpr, Hprback⟩
      iNamed Hpr
      have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
      wp_auto
      rw [Hnolearner]
      ihave Htrk := Hprback $$ [Hpv Hinfl]
      · iapply ownProgress_intro $$ Hpv Hinfl
        ipureintro; exact Habs
      ihave Hphys := Hback $$ %tv3 Htrkf Htrk
      wp_apply raft.wp_store_isLearner $$ Hphys as Hphys
      wp_apply raft.wp_load_isLearner $$ Hphys as Hphys
      wp_apply raft.wp_load_state $$ Hphys as Hphys
      rw [decide_eq_false Hns]
      wp_auto
      iapply HΦ $$ %cs %xs %s1
      iframe
      ipureintro
      exact ⟨Hxs, Hcs0, HSw⟩
    | none =>
      simp only [Option.getD_none, Option.isSome_none]
      wp_auto
      ihave Hphys := Hback $$ %tv3 Htrkf Htrk
      wp_apply raft.wp_store_isLearner $$ Hphys as Hphys
      -- `!ok` is `true`: the `||` does not load `r.isLearner`, and `r.state` is loaded by
      -- both `if`s
      wp_apply raft.wp_load_state $$ Hphys as Hphys
      rw [decide_eq_false Hns]
      wp_auto
      wp_apply raft.wp_load_state $$ Hphys as Hphys
      rw [decide_eq_false Hns]
      wp_auto
      iapply HΦ $$ %cs %xs %s1
      iframe
      ipureintro
      exact ⟨Hxs, Hcs0, HSw⟩

end proof

end EtcdGrove
end Perennial
