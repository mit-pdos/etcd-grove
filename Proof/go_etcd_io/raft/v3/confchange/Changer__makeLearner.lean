/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__makeLearner.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeLearner
public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.Changer__remove
public import Spec.go_etcd_io.raft.v3.confchange.outgoing
public import Spec.go_etcd_io.raft.v3.confchange.nilAwareAdd

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

theorem confchange.Changer.makeLearner.wp_proof
    (wp_Changer_initProgress : confchange.Changer.initProgress.spec (GF := GF) (hG := hG))
    (wp_Changer_remove : confchange.Changer.remove.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG))
    (wp_confchange_nilAwareAdd : confchange.nilAwareAdd.spec (GF := GF) (hG := hG)) :
    confchange.Changer.makeLearner.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg base s id dq Hmi
  wp_start as ⟨Hp, Hw⟩
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg, %prs, %pvs, Hcfgp, Hc, Htrk, Hprs, %Hflags, Hnew⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `pr := trk[id]`
  wp_apply wp_map_lookup1 $$ Htrk as Htrk
  rcases Hlk : prs !! id with _ | pr
  · -- a new id: `initProgress(..., true)`
    simp only [Option.getD_none]
    wp_auto
    have Hid : id ∉ s.prs := by
      rw [← Hflags, flagsOf_mem]
      intro h; rw [← Hdom, Hlk] at h; cases h
    have Hsn : s.prs !! id = none := by
      rcases h : s.prs !! id with _ | b
      · rfl
      · exact absurd (by rw [GMap.mem_iff, h]; rfl) Hid
    ihave Hw := ownWork_intro chg base cfgp trk s cfg prs pvs Hflags $$ Hcfgp Hc Htrk Hprs Hnew
    wp_apply wp_Changer_initProgress c_ptr cfgp trk chg base s id true _ Hid Hmi
      $$ [$c $Hw] as ⟨c, Hw⟩
    iapply HΦ
    iframe Hp
    simp only [makeLearnerM, Hsn]
    iexact Hw
  · simp only [Option.getD_some]
    obtain ⟨pv, Hpv⟩ : ∃ pv, pvs !! id = some pv :=
      Option.isSome_iff_exists.1 ((Hdom id).1 (by rw [Hlk]; rfl))
    have Hsl : s.prs !! id = some pv.IsLearner' := by rw [← Hflags]; exact flagsOf_lookup pvs id pv Hpv
    have Hmem : id ∈ s.prs := by rw [GMap.mem_iff, Hsl]; rfl
    icases ownPrs_borrow chg base prs pvs id pr pv Hlk Hpv $$ [$Hprs $Hnew] with ⟨Hpr, Hback⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %Hprnn⟩
    wp_if_destruct
    · exact absurd rfl Hprnn
    have Hpv_eq : ∀ b, pv.IsLearner' = b → ({ pv with IsLearner' := b } : tracker.Progress) = pv := by
      intro b hb; rw [← hb]
    cases hl : pv.IsLearner'
    · -- not a learner: removed, its `Progress` kept, then staged or made a learner
      wp_auto
      have Hdomeq : domSet prs = domSet s.prs := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_dom', GMap.elem_of_dom', ← Hflags, flagsOf_mem]
        exact Hdom k
      ihave Hcw : ownCfgAt cfgp s.cfg $$ [Hcfgp Hc]
      · unfold ownCfgAt; iexists cfg; iframe
      wp_apply wp_Changer_remove c_ptr cfgp trk chg s prs id _ Hdomeq $$ [$c $Hcw $Htrk]
        as ⟨c, Hcw, Htrk⟩
      wp_apply wp_mapInsert $$ Htrk as Htrk
      have Hprs' : <[id := pr]> (if id ∈ s.prs ∧ id ∉ s.cfg.outgoing then GMap.delete id prs
          else prs) = prs := by
        split
        · rw [GMap.insert_delete_eq, GMap.insert_id _ _ _ Hlk]
        · rw [GMap.insert_id _ _ _ Hlk]
      rw [Hprs']
      unfold ownCfgAt
      icases Hcw with ⟨%cfg1, Hcfgp, Hc⟩
      icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
      simp only [removeM, if_pos Hmem, removeCfg.proj_incoming, removeCfg.proj_outgoing,
        removeCfg.proj_learners, removeCfg.proj_learnersNext, removeCfg.proj_autoLeave] at Hal ⊢
      wp_auto
      wp_apply wp_confchange_outgoing _ vin vout Harr
      icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
      wp_apply wp_idset_lookup2 $$ Hout as Hout
      ihave Hout := ownIdsetC_join _ _ _ Hcout $$ Hout
      icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn⟩
      iStructNamed Hcfgp
      wp_if_destruct
      · -- an outgoing voter: staged in `LearnersNext`
        have Hon : id ∈ s.cfg.outgoing := by simpa [GMap.mem_iff] using Hif
        ihave Hln := ownIdsetC_Q _ _ _ $$ Hln
        wp_apply wp_confchange_nilAwareAdd $$ [$LearnersNext $Hln] as %mln ⟨LearnersNext, Hln⟩
        ihave Hcfgp : (cfgp ↦ ({ cfg1 with LearnersNext' := mln } : tracker.Config)) $$
            [Voters AutoLeave Learners LearnersNext]
        · iapply typedPointsto_combine _ _ _ Hcnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave Hln : ownIdsetC mln (DFrac.own 1) (<[id := ()]> (GMap.delete id s.cfg.learnersNext))
          $$ [Hln]
        · unfold ownIdsetC; iright; iframe Hln; ipureintro
          intro h
          have := congrArg (fun m => m !! id) h
          simp at this
        icases Hback $$ %false [Hpr] with ⟨Hprs, Hnew⟩
        · rw [Hpv_eq false hl]; iexact Hpr
        rw [Hpv_eq false hl, GMap.insert_id _ _ _ Hpv]
        iapply HΦ
        iframe Hp
        have Hst : makeLearnerM id s =
            ⟨⟨GMap.delete id s.cfg.incoming, s.cfg.outgoing, GMap.delete id s.cfg.learners,
              <[id := ()]> (GMap.delete id s.cfg.learnersNext), s.cfg.autoLeave⟩, s.prs⟩ := by
          simp [makeLearnerM, Hsl, hl, Hon, removeCfg]
        iapply ownWork_intro chg base cfgp trk (makeLearnerM id s) _ prs pvs
          (by rw [Hst]; exact Hflags) $$ Hcfgp [Hin Hout Hl Hln] Htrk Hprs Hnew
        iapply ownCfgCC_intro ({ cfg1 with LearnersNext' := mln } : tracker.Config) (DFrac.own 1)
          (makeLearnerM id s).cfg vin vout Harr (by rw [Hst]; exact Hal) $$ [Hin] [Hout] [Hl] [Hln]
        all_goals rw [Hst]
        · iexact Hin
        · iexact Hout
        · iexact Hl
        · iexact Hln
      · -- not an outgoing voter: a learner
        have Hon : id ∉ s.cfg.outgoing := by simpa [GMap.mem_iff] using Hif
        ihave Hl := ownIdsetC_Q _ _ _ $$ Hl
        wp_apply wp_confchange_nilAwareAdd $$ [$Learners $Hl] as %ml ⟨Learners, Hl⟩
        ihave Hcfgp : (cfgp ↦ ({ cfg1 with Learners' := ml } : tracker.Config)) $$
            [Voters AutoLeave Learners LearnersNext]
        · iapply typedPointsto_combine _ _ _ Hcnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave Hl := ownIdsetC_insert _ _ _ _ $$ Hl
        icases Hback $$ %true Hpr with ⟨Hprs, Hnew⟩
        iapply HΦ
        iframe Hp
        have Hst : makeLearnerM id s =
            ⟨⟨GMap.delete id s.cfg.incoming, s.cfg.outgoing,
              <[id := ()]> (GMap.delete id s.cfg.learners), GMap.delete id s.cfg.learnersNext,
              s.cfg.autoLeave⟩, <[id := true]> s.prs⟩ := by
          simp [makeLearnerM, Hsl, hl, Hon, removeCfg]
        iapply ownWork_intro chg base cfgp trk (makeLearnerM id s) _ prs _
          (by rw [Hst]; simp only [flagsOf_insert, Hflags]) $$ Hcfgp [Hin Hout Hl Hln] Htrk Hprs Hnew
        iapply ownCfgCC_intro ({ cfg1 with Learners' := ml } : tracker.Config) (DFrac.own 1)
          (makeLearnerM id s).cfg vin vout Harr (by rw [Hst]; exact Hal) $$ [Hin] [Hout] [Hl] [Hln]
        all_goals rw [Hst]
        · iexact Hin
        · iexact Hout
        · iexact Hl
        · iexact Hln
    · -- already a learner: nothing
      wp_auto
      icases Hback $$ %true [Hpr] with ⟨Hprs, Hnew⟩
      · rw [Hpv_eq true hl]; iexact Hpr
      rw [Hpv_eq true hl, GMap.insert_id _ _ _ Hpv]
      iapply HΦ
      iframe Hp
      have Hst : makeLearnerM id s = s := by simp [makeLearnerM, Hsl, hl]
      rw [Hst]
      iapply ownWork_intro chg base cfgp trk s cfg prs pvs Hflags $$ Hcfgp Hc Htrk Hprs Hnew

end proof

end EtcdGrove
end Perennial
