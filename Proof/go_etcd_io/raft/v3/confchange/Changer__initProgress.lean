/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__initProgress.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.tracker.NewInflights
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

theorem confchange.Changer.initProgress.wp_proof
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_tracker_NewInflights : tracker.NewInflights.spec (GF := GF) (hG := hG))
    (wp_confchange_nilAwareAdd : confchange.nilAwareAdd.spec (GF := GF) (hG := hG)) :
    confchange.Changer.initProgress.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg base s id b dq Hid Hmi
  wp_start as ⟨Hp, Hw⟩
  unfold ownWork ownCfgAt ownPrsW
  icases Hw with ⟨⟨%cfg, Hcfgp, Hc⟩, ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩⟩
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hpvnone : pvs !! id = none := by
    have h : ¬ (flagsOf pvs !! id).isSome := by rw [Hflags]; exact Hid
    rw [flagsOf, GMap.lookup_fmap] at h
    cases h' : pvs !! id with
    | none => rfl
    | some _ => rw [h'] at h; simp at h
  have Hprnone : prs !! id = none := by
    have h := Hdom0 id
    change (prs !! id).isSome = true ↔ (pvs !! id).isSome = true at h
    rw [Hpvnone] at h
    cases h' : prs !! id with
    | none => rfl
    | some _ => rw [h'] at h; simp at h
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  cases b
  · -- a voter: into the incoming voters
    wp_auto
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_mapInsert $$ Hin as Hin
    -- `max(c.LastIndex, 1)`: Goose's `max` is stepped into
    wp_func_call
    wp_call
    wp_if_destruct
    all_goals
      wp_apply wp_tracker_NewInflights _ _ Hmi as %il Hinfl
      wp_apply wp_mapInsert $$ Htrk as Htrk
      iapply HΦ
      iframe Hp
      simp only [initProgressM.proj_cfg, initProgressM.proj_prs, Bool.false_eq_true, ↓reduceIte]
      isplitl [Hcfgp Hin Hout Hl Hln]
      · iexists cfg
        iframe Hcfgp
        iapply ownCfgCC_intro cfg (DFrac.own 1)
          { s.cfg with incoming := <[id := ()]> s.cfg.incoming } vin vout Harr Hal
          $$ Hin Hout Hl Hln
      iexists _, _
      iframe Htrk
      isplitl [Hprs «$r0»]
      · iapply (BigSepM2.bigSepM2_insert Hprnone Hpvnone).2
        iframe
      simp only [pm_insert_gmap]
      isplitr
      · ipureintro
        rw [← Hflags]
        apply GMap.map_eq; intro k
        by_cases hk : id = k
        · subst hk; simp [flagsOf]
        · simp [flagsOf, hk]
      iapply (BigSepM.bigSepM_insert Hpvnone).2
      iframe Hnew
      unfold ownNewPr
      iright
      iframe Hinfl
      ipureintro
      refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
      word
  · -- a learner: `nilAwareAdd(&cfg.Learners, id)`
    wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn⟩
    iStructNamed Hcfgp
    ihave Hl := ownIdsetC_Q _ _ _ $$ Hl
    wp_apply wp_confchange_nilAwareAdd $$ [$Learners $Hl] as %m' ⟨Learners, Hl⟩
    ihave Hcfgp : (cfgp ↦ ({ cfg with Learners' := m' } : tracker.Config)) $$
        [Voters AutoLeave Learners LearnersNext]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hl := ownIdsetC_insert _ _ _ _ $$ Hl
    wp_func_call
    wp_call
    wp_if_destruct
    all_goals
      wp_apply wp_tracker_NewInflights _ _ Hmi as %il Hinfl
      wp_apply wp_mapInsert $$ Htrk as Htrk
      iapply HΦ
      iframe Hp
      simp only [initProgressM.proj_cfg, initProgressM.proj_prs, ↓reduceIte]
      isplitl [Hcfgp Hin Hout Hl Hln]
      · iexists ({ cfg with Learners' := m' } : tracker.Config)
        iframe Hcfgp
        iapply ownCfgCC_intro ({ cfg with Learners' := m' } : tracker.Config) (DFrac.own 1)
          { s.cfg with learners := <[id := ()]> s.cfg.learners } vin vout Harr Hal
          $$ Hin Hout Hl Hln
      iexists _, _
      iframe Htrk
      isplitl [Hprs «$r0»]
      · iapply (BigSepM2.bigSepM2_insert Hprnone Hpvnone).2
        iframe
      simp only [pm_insert_gmap]
      isplitr
      · ipureintro
        rw [← Hflags]
        apply GMap.map_eq; intro k
        by_cases hk : id = k
        · subst hk; simp [flagsOf]
        · simp [flagsOf, hk]
      iapply (BigSepM.bigSepM_insert Hpvnone).2
      iframe Hnew
      unfold ownNewPr
      iright
      iframe Hinfl
      ipureintro
      refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
      word

end proof

end EtcdGrove
end Perennial
