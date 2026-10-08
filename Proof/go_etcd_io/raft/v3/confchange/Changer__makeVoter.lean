/-
Proof of `Spec/Changer__makeVoter.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeVoter
public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.incoming
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

theorem confchange.Changer.makeVoter.wp_proof
    (wp_Changer_initProgress : confchange.Changer.initProgress.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_nilAwareDelete : confchange.nilAwareDelete.spec (GF := GF) (hG := hG)) :
    confchange.Changer.makeVoter.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk v chg cfg id vm prs dq Hcfg Hdom Hmi
  have Hcfg' := Hcfg
  obtain ⟨⟨Harr, Hl, Hln⟩, Hal⟩ := Hcfg'
  wp_start as ⟨Hp, Hcfgp, Hv, Htrk, Hprogs⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `pr := trk[id]`
  wp_apply wp_map_lookup1 $$ Htrk as Htrk
  rcases Hlk : prs !! id with _ | pr
  · -- a new id: `initProgress`
    simp only [Option.getD_none]
    wp_auto
    -- `c.initProgress(...)` on the local copy of the receiver
    wp_apply wp_Changer_initProgress c_ptr _ _ v _ _ _ _ _ _ Hcfg Hmi $$ [$c $Hcfgp $Hv $Htrk]
      as %pr %pp ⟨c, Hcfgp, Hv, Htrk, Hpr⟩
    iapply HΦ
    iframe Hp Hcfgp Hv Htrk
    isplitr
    · ipureintro
      rw [GMap.dom_insert, GMap.dom_insert, Hdom]
    iapply (BigSepM.bigSepM_insert (Φ := fun _ pr => iprop(∃ pp, ownProgress pr pp)) Hlk).2
    iframe Hprogs
    iexists pp
    iexact Hpr
  · -- a repeated voter: its `Progress` stays, re-marked a non-learner (it already is
    -- one), the learner maps are `nil`
    simp only [Option.getD_some]
    icases (BigSepM.bigSepM_delete (Φ := fun _ pr => iprop(∃ pp, ownProgress pr pp)) (m := prs)
      Hlk).1 $$ Hprogs with ⟨⟨%pp, Hpr⟩, Hprogs⟩
    iNamed Hpr
    icases typedPointsto_not_null_dup _ _ _ $$ Hpv with ⟨Hpv, %Hprnn⟩
    wp_if_destruct
    · exact absurd rfl Hprnn
    -- `nilAwareDelete(&cfg.Learners, id)`, `nilAwareDelete(&cfg.LearnersNext, id)`
    icases (Access.access (A := iprop(cfgp.[tracker.Config, go!"Learners"] ↦ cfg.Learners'))
      (A' := iprop(cfgp.[tracker.Config, go!"Learners"] ↦ cfg.Learners'))
      (P := iprop(cfgp ↦ cfg))) $$ Hcfgp with ⟨Hf, Hback⟩
    rw [Hl]
    wp_apply wp_confchange_nilAwareDelete $$ [$Hf] as Hf
    rw [← Hl]
    ihave Hcfgp := Hback $$ Hf
    icases (Access.access (A := iprop(cfgp.[tracker.Config, go!"LearnersNext"] ↦ cfg.LearnersNext'))
      (A' := iprop(cfgp.[tracker.Config, go!"LearnersNext"] ↦ cfg.LearnersNext'))
      (P := iprop(cfgp ↦ cfg))) $$ Hcfgp with ⟨Hf, Hback⟩
    rw [Hln]
    wp_apply wp_confchange_nilAwareDelete $$ [$Hf] as Hf
    rw [← Hln]
    ihave Hcfgp := Hback $$ Hf
    wp_auto
    wp_apply wp_confchange_incoming _ v map.nil Harr
    wp_apply wp_mapInsert $$ Hv as Hv
    iapply HΦ
    iframe Hp Hcfgp Hv Htrk
    have Hid_vm : vm !! id = some () := by
      have h1 : id ∈ domSet prs := GMap.elem_of_dom_2 _ _ _ Hlk
      rw [Hdom, GMap.elem_of_dom] at h1
      obtain ⟨⟨⟩, h⟩ := h1
      exact h
    isplitr
    · ipureintro
      rw [GMap.dom_insert_lookup _ _ _ _ Hid_vm]
      exact Hdom
    iapply (BigSepM.bigSepM_delete (Φ := fun _ pr => iprop(∃ pp, ownProgress pr pp)) (m := prs)
      Hlk).2
    iframe Hprogs
    iexists pp
    have Hpv_learner : pv.IsLearner' = false := ((progressAbs_Some _ _ _).1 Habs).1
    iapply ownProgress_intro _ _ pp $$ Hpv Hinfl
    ipureintro
    rw [show ({ pv with IsLearner' := false } : tracker.Progress) = pv by
      rw [← Hpv_learner]]
    exact Habs
