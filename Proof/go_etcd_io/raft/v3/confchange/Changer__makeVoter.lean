/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__makeVoter.lean`. Lean-first (no Rocq counterpart).
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
  · -- a new id: `initProgress`
    simp only [Option.getD_none]
    wp_auto
    have Hid : id ∉ s.prs := by
      rw [← Hflags, flagsOf_mem]
      intro h; rw [← Hdom, Hlk] at h; cases h
    ihave Hw := ownWork_intro chg base cfgp trk s cfg prs pvs Hflags $$ Hcfgp Hc Htrk Hprs Hnew
    wp_apply wp_Changer_initProgress c_ptr cfgp trk chg base s id false _ Hid Hmi
      $$ [$c $Hw] as ⟨c, Hw⟩
    iapply HΦ
    iframe Hp
    simp only [makeVoterM, if_neg Hid]
    iexact Hw
  · -- a tracked id: marked a non-learner, out of the learner sets, an incoming voter
    simp only [Option.getD_some]
    obtain ⟨pv, Hpv⟩ : ∃ pv, pvs !! id = some pv :=
      Option.isSome_iff_exists.1 ((Hdom id).1 (by rw [Hlk]; rfl))
    have Hmem : id ∈ s.prs := by
      rw [← Hflags, flagsOf_mem, Hpv]; rfl
    icases ownPrs_borrow chg base prs pvs id pr pv Hlk Hpv $$ [$Hprs $Hnew] with ⟨Hpr, Hback⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %Hprnn⟩
    wp_if_destruct
    · exact absurd rfl Hprnn
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn⟩
    iStructNamed Hcfgp
    icases Hback $$ %false Hpr with ⟨Hprs, Hnew⟩
    ihave Hl := ownIdsetC_Q _ _ _ $$ Hl
    wp_apply wp_confchange_nilAwareDelete $$ [$Learners $Hl] as %ml ⟨Learners, Hl⟩
    ihave Hln := ownIdsetC_Q _ _ _ $$ Hln
    wp_apply wp_confchange_nilAwareDelete $$ [$LearnersNext $Hln] as %mln ⟨LearnersNext, Hln⟩
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_mapInsert $$ Hin as Hin
    ihave Hcfgp : (cfgp ↦ ({ cfg with Learners' := ml, LearnersNext' := mln } : tracker.Config)) $$
        [Voters AutoLeave Learners LearnersNext]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc : ownCfgCC ({ cfg with Learners' := ml, LearnersNext' := mln } : tracker.Config)
        (DFrac.own 1) (makeVoterM id s).cfg $$ [Hin Hout Hl Hln]
    · iapply ownCfgCC_intro ({ cfg with Learners' := ml, LearnersNext' := mln } : tracker.Config)
        (DFrac.own 1) (makeVoterM id s).cfg vin vout Harr (by simp [makeVoterM, Hmem, Hal])
        $$ [Hin] [Hout] [Hl] [Hln]
      all_goals simp only [makeVoterM, if_pos Hmem]
      · iexact Hin
      · iexact Hout
      · iexact Hl
      · iexact Hln
    iapply HΦ
    iframe Hp
    iapply ownWork_intro chg base cfgp trk (makeVoterM id s) _ prs _ ?_
      $$ Hcfgp Hc Htrk Hprs Hnew
    simp only [makeVoterM, if_pos Hmem, flagsOf_insert, Hflags]

end proof

end EtcdGrove
end Perennial
