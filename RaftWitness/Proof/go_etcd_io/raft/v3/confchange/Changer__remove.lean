/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__remove.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__remove
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.confchange.outgoing
public import Spec.go_etcd_io.raft.v3.confchange.nilAwareDelete

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

theorem confchange.Changer.remove.wp_proof
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG))
    (wp_confchange_nilAwareDelete : confchange.nilAwareDelete.spec (GF := GF) (hG := hG)) :
    confchange.Changer.remove.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg s prs id dq Hdomeq
  wp_start as ⟨Hp, Hw, Htrk⟩
  unfold ownCfgAt
  icases Hw with ⟨%cfg, Hcfgp, Hc⟩
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_map_lookup2 $$ Htrk as Htrk
  wp_if_destruct
  · -- `id` is tracked
    have Hmem : id ∈ s.prs := (mem_of_domSet_eq Hdomeq id).1 ((GMap.mem_iff prs id).2 (by simpa using Hif))
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_mapDelete_named quorum.MajorityConfig.ty go.uint64 (go.GoType.StructType [])
      $$ Hin as Hin
    icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn⟩
    iStructNamed Hcfgp
    ihave Hl := ownIdsetC_Q _ _ _ $$ Hl
    wp_apply wp_confchange_nilAwareDelete $$ [$Learners $Hl] as %ml ⟨Learners, Hl⟩
    ihave Hln := ownIdsetC_Q _ _ _ $$ Hln
    wp_apply wp_confchange_nilAwareDelete $$ [$LearnersNext $Hln] as %mln ⟨LearnersNext, Hln⟩
    -- raft#168: `if id == cfg.Witnesses[0] { cfg.Witnesses[0] = 0 }` (2026-10-20: at any witness)
    icases array_acc _ (sint.Z (W64 0)) _ _ _ s.cfg.wit (by decide) (by rw [Hwit.1]; rfl)
      $$ Witnesses with ⟨Hw0, Hwback⟩
    wp_auto
    by_cases Hidw : id = s.cfg.wit
    rw [decide_eq_true Hidw]
    wp_auto
    ihave Witnesses := Hwback $$ Hw0
    have HW' : (array.mk 2 (cfg.Witnesses'.arr.set (sint.Z (W64 0)).toNat (W64 0)) :
        GoArray w64 2).arr = [(removeCfg id s.cfg).wit, W64 0] ∧
        ((removeCfg id s.cfg).wit ≠ W64 0 → (removeCfg id s.cfg).wit ∈ (removeCfg id s.cfg).incoming) := by
      simp only [removeCfg, if_pos Hidw]
      refine ⟨?_, fun h => absurd rfl h⟩
      show cfg.Witnesses'.arr.set _ _ = _
      rw [Hwit.1]; rfl
    generalize (array.mk 2 (cfg.Witnesses'.arr.set (sint.Z (W64 0)).toNat (W64 0)) :
      GoArray w64 2) = W' at HW'
    rotate_left
    rw [decide_eq_false Hidw]
    wp_auto
    ihave Witnesses := Hwback $$ Hw0
    rw [list_set_lookup_self _ _ _ (show cfg.Witnesses'.arr[(sint.Z (W64 0)).toNat]? = some s.cfg.wit by
      rw [Hwit.1]; rfl)]
    have HW' : (array.mk 2 cfg.Witnesses'.arr : GoArray w64 2).arr = [(removeCfg id s.cfg).wit, W64 0] ∧
        ((removeCfg id s.cfg).wit ≠ W64 0 → (removeCfg id s.cfg).wit ∈ (removeCfg id s.cfg).incoming) := by
      simp only [removeCfg, if_neg Hidw]
      refine ⟨Hwit.1, fun h => ?_⟩
      rw [GMap.elem_of_gset, GMap.lookup_delete_ne _ Hidw, ← GMap.elem_of_gset]
      exact Hwit.2 h
    generalize (array.mk 2 cfg.Witnesses'.arr : GoArray w64 2) = W' at HW'
    all_goals
      wp_apply wp_confchange_outgoing _ vin vout Harr
      icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
      wp_apply wp_idset_lookup2 $$ Hout as Hout
      ihave Hout := ownIdsetC_join _ _ _ Hcout $$ Hout
      ihave Hcfgp : (cfgp ↦ ({ cfg with Learners' := ml, LearnersNext' := mln, Witnesses' := W' } :
          tracker.Config)) $$
          [Voters AutoLeave Learners LearnersNext Witnesses]
      · iapply typedPointsto_combine _ _ _ Hcnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_if_destruct
      · -- an outgoing voter: its `Progress` stays
        iapply HΦ
        iframe Hp
        have Hout' : id ∈ s.cfg.outgoing := by simpa [GMap.mem_iff] using Hif
        rw [ite_eq_right (fun h => h.2 Hout')]
        iframe Htrk
        simp only [removeM, ite_eq_left Hmem]
        iexists ({ cfg with Learners' := ml, LearnersNext' := mln, Witnesses' := W' } : tracker.Config)
        iframe Hcfgp
        iapply ownCfgCC_intro ({ cfg with Learners' := ml, LearnersNext' := mln, Witnesses' := W' } :
          tracker.Config) (DFrac.own 1) (removeCfg id s.cfg) vin vout Harr Hal HW' $$ [Hin] [Hout] [Hl] [Hln]
        all_goals simp only [removeCfg.proj_incoming, removeCfg.proj_outgoing,
          removeCfg.proj_learners, removeCfg.proj_learnersNext]
        · iexact Hin
        · iexact Hout
        · iexact Hl
        · iexact Hln
      · -- not an outgoing voter: untracked
        wp_apply wp_mapDelete_named tracker.ProgressMap.ty go.uint64
          (go.GoType.PointerType tracker.Progress.ty) $$ Htrk as Htrk
        iapply HΦ
        iframe Hp
        have Hout' : id ∉ s.cfg.outgoing := by simpa [GMap.mem_iff] using Hif
        rw [ite_eq_left ⟨Hmem, Hout'⟩]
        iframe Htrk
        simp only [removeM, ite_eq_left Hmem]
        iexists ({ cfg with Learners' := ml, LearnersNext' := mln, Witnesses' := W' } : tracker.Config)
        iframe Hcfgp
        iapply ownCfgCC_intro ({ cfg with Learners' := ml, LearnersNext' := mln, Witnesses' := W' } :
          tracker.Config) (DFrac.own 1) (removeCfg id s.cfg) vin vout Harr Hal HW' $$ [Hin] [Hout] [Hl] [Hln]
        all_goals simp only [removeCfg.proj_incoming, removeCfg.proj_outgoing,
          removeCfg.proj_learners, removeCfg.proj_learnersNext]
        · iexact Hin
        · iexact Hout
        · iexact Hl
        · iexact Hln
  · -- untracked: nothing
    have Hmem : id ∉ s.prs := fun h => Hif (by
      have := (GMap.mem_iff prs id).1 ((mem_of_domSet_eq Hdomeq id).2 h); simpa using this)
    iapply HΦ
    iframe Hp
    rw [ite_eq_right (fun h => Hmem h.1)]
    iframe Htrk
    simp only [removeM, ite_eq_right Hmem]
    iexists cfg
    iframe Hcfgp
    iapply ownCfgCC_intro cfg (DFrac.own 1) s.cfg vin vout Harr Hal Hwit $$ Hin Hout Hl Hln

end proof

end EtcdGrove
end Perennial
