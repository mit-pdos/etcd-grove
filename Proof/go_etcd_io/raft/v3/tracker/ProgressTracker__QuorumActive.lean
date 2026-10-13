/-
`tracker.ProgressTracker.QuorumActive`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__QuorumActive
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__VoteResult

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `Visit`, with the caller invariant that the local `votes` map has visited voters as its
domain (and the `Progress` values are unchanged: the closure only reads its `Progress`; a
learner, `IsLearner` set by `LearnerFlagsC`, is skipped); then `JointConfig.VoteResult` on
the tracker's `JointConfig` and the fresh `votes` map (since 2026-10-13 its spec is general;
until then this proof inlined it). -/
theorem tracker.ProgressTracker.QuorumActive.wp_proof
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_JointConfig_VoteResult : quorum.JointConfig.VoteResult.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.QuorumActive.spec (GF := GF) (hG := hG) := by
  intro c trk tv t
  wp_start as ⟨Htrk, Hown⟩
  icases ownTrackerC_pure c tv t $$ Hown with ⟨%Hpure, Hown⟩
  obtain ⟨-, Hdom0, Hfl, -, -⟩ := Hpure
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %vref Hvm
  wp_apply wp_ProgressTracker_Visit c _ tv t _
      (fun _ pvsx => iprop(∃ (vm : GMap w64 Bool),
        "votes" ∷ votes_ptr ↦ vref ∗
        "Hvm" ∷ vref ↦$ vm ∗
        "%Hvdom" ∷ ⌜domSet vm ⊆ c.voters⌝ ∗
        "%Hpvs" ∷ ⌜pvsx = t.peers⌝))
    $$ [$Htrk $Hown votes Hvm]
  · isplitl [votes Hvm]
    · iexists ∅
      simp only [named]
      iframe votes Hvm
      ipureintro
      exact ⟨by rw [GMap.dom_empty]; exact GMap.empty_subseteq _, trivial⟩
    imodintro
    unfold visitClosureC
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback, HI⟩
    iNamed HI
    iunfold ownProgress at Hpr
    iNamed Hpr
    have Habs' := (progressAbs_Some _ _ _).1 Habs
    have Hpl : p.learner = decide (i ∈ c.learners) := Hfl i p (Hpvs ▸ Hpvi)
    wp_auto
    by_cases Hic : i ∈ c.learners
    · have Hb : pv.IsLearner' = true := by
        rw [Habs'.1, Hpl]; exact decide_eq_true Hic
      rw [Hb]
      wp_auto
      ihave Hpr := ownProgress_intro pr pv p $$ Hpv Hinfl []
      · ipureintro; exact Habs
      ihave Htrk := Hback $$ %p Hpr %rfl
      rw [GMap.insert_id pvs0 i p Hpvi]
      iapply HΦ
      iexists tv0, pvs0
      iframe Htrkf Htrk
      iexists vm
      simp only [named]
      iframe votes Hvm
      ipureintro
      exact ⟨Hvdom, Hpvs⟩
    · have Hb : pv.IsLearner' = false := by
        rw [Habs'.1, Hpl]; exact decide_eq_false Hic
      -- a tracked non-learner is a voter
      have Hiv : i ∈ c.voters := by
        rw [Hdom0] at Hicfg
        unfold CfgM.ids at Hicfg
        rcases (GMap.elem_of_union _ _ _).1 Hicfg with h | h
        · exact h
        · exact absurd h Hic
      rw [Hb]
      wp_auto
      wp_apply wp_mapInsert $$ [$Hvm] as Hvm
      ihave Hpr := ownProgress_intro pr pv p $$ Hpv Hinfl []
      · ipureintro; exact Habs
      ihave Htrk := Hback $$ %p Hpr %rfl
      rw [GMap.insert_id pvs0 i p Hpvi]
      iapply HΦ
      iexists tv0, pvs0
      iframe Htrkf Htrk
      iexists (<[i := pv.RecentActive']> vm)
      simp only [named]
      iframe votes Hvm
      ipureintro
      refine ⟨?_, Hpvs⟩
      rw [GMap.dom_insert, GMap.union_subseteq]
      exact ⟨(GMap.singleton_subseteq_l _ _).2 Hiv, Hvdom⟩
  iintro ⟨%tvfin, %pvsfin, Htrk, Hown, HI⟩
  iNamed HI
  subst Hpvs
  iunfold ownTrackerC at Hown
  iNamed Hown
  simp only at Hinv Hdom Hflags Hsize
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  have Hsz0 : (GMap.size c.incoming : Int) < 2 ^ 63 := by
    have := size_le_of_sub_dom c.incoming t.prs (by rw [Hdom]; exact incoming_sub_ids c)
    omega
  have Hsz1 : (GMap.size c.outgoing : Int) < 2 ^ 63 := by
    have := size_le_of_sub_dom c.outgoing t.prs (by rw [Hdom]; exact outgoing_sub_ids c)
    omega
  wp_auto
  icases (tracker.ProgressTracker.ProgressTracker_access_load_Config trk tvfin (DFrac.own 1)).access_strict
    $$ Htrk with ⟨Hcfgf, Hback1⟩
  icases (tracker.Config.Config_access_load_Voters _ tvfin.Config' (DFrac.own 1)).access_strict
    $$ Hcfgf with ⟨Hvf, Hback2⟩
  wp_apply wp_JointConfig_VoteResult _ (DFrac.own 1) _ vin vout c.incoming c.outgoing vref
      (DFrac.own 1) vm Harr Hsz0 Hsz1 $$ [$Hvf $Hv0 $Hv1 $Hvm]
    as %res ⟨Hvf, Hv0, Hv1, Hvm, %Hres, %Hwon, -⟩
  ihave Hcfgf := Hback2 $$ Hvf
  ihave Htrk := Hback1 $$ Hcfgf
  ihave Hcfg := Hcback $$ Hv0 Hv1
  ihave Hown := ownTrackerC_intro c tvfin t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg
  have Hsub : granted vm ⊆ c.voters := by
    rw [GMap.elem_of_subseteq]
    intro x hx
    rw [elem_of_granted] at hx
    exact (GMap.elem_of_subseteq _ _).1 Hvdom _ ((GMap.elem_of_dom _ _).2 ⟨_, hx⟩)
  iapply HΦ $$ %(decide (res = W8 3)) %tvfin %(granted vm)
  iframe Htrk Hown
  ipureintro
  exact ⟨Hsub, decide_eq_true_iff.trans Hwon⟩

end proof

end EtcdGrove
end Perennial
