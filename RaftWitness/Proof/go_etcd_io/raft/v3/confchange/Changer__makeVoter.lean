/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__makeVoter.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeVoter
public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.confchange.nilAwareDelete
public import Spec.fmt.Errorf

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
    (wp_confchange_nilAwareDelete : confchange.nilAwareDelete.spec (GF := GF) (hG := hG))
    (wp_fmt_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    confchange.Changer.makeVoter.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg base s id dq Hmi
  wp_start as ⟨Hp, Hw⟩
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg, %prs, %pvs, Hcfgp, Hc, Htrk, Hprs, %Hflags, %Hwt, Hnew⟩
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
    ihave Hw := ownWork_intro chg base cfgp trk s cfg prs pvs Hflags Hwt $$ Hcfgp Hc Htrk Hprs Hnew
    wp_apply wp_Changer_initProgress c_ptr cfgp trk chg base s id false false _ Hid
      (fun h => absurd h (by decide)) Hmi
      $$ [$c $Hw] as ⟨c, Hw⟩
    iapply HΦ
    iframe Hp
    simp only [makeVoterO, makeVoterM, ite_eq_right Hid]
    rw [ite_eq_right (fun h => Hid h.1)]
    simp only [ownWorkO]
    iframe Hw
    try (ipureintro; rfl)
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
    -- `if pr.IsWitness` (2026-10-20, witness support): at the witness, an error
    have Hpvw := Hwt.2 id pv Hpv
    by_cases Hw : id = s.cfg.wit ∧ s.cfg.wit ≠ W64 0
    · rw [show (#pv.IsWitness' : val) = #true by rw [Hpvw, decide_eq_true Hw]]
      wp_auto
      ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
      wp_apply wp_fmt_Errorf $$ [$Hnil] as %e -
      · fmt_args_ok
      iapply HΦ
      iframe Hp
      have Hc : id ∈ s.prs ∧ id = s.cfg.wit ∧ s.cfg.wit ≠ W64 0 := ⟨Hmem, Hw⟩
      simp only [makeVoterO, if_pos Hc, ownWorkO]
      ipureintro; intro h; cases h
    rw [show (#pv.IsWitness' : val) = #false by rw [Hpvw, decide_eq_false Hw]]
    wp_auto
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
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
        [Voters AutoLeave Learners LearnersNext Witnesses]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc : ownCfgCC ({ cfg with Learners' := ml, LearnersNext' := mln } : tracker.Config)
        (DFrac.own 1) (makeVoterM id s).cfg $$ [Hin Hout Hl Hln]
    · iapply ownCfgCC_intro ({ cfg with Learners' := ml, LearnersNext' := mln } : tracker.Config)
        (DFrac.own 1) (makeVoterM id s).cfg vin vout Harr (by simp [makeVoterM, Hmem, Hal])
        (by simp only [makeVoterM, ite_eq_left Hmem]
            exact ⟨Hwit.1, fun h => (gset_mem_insert _ _ _).2 (.inr (Hwit.2 h))⟩)
        $$ [Hin] [Hout] [Hl] [Hln]
      all_goals simp only [makeVoterM, ite_eq_left Hmem]
      · iexact Hin
      · iexact Hout
      · iexact Hl
      · iexact Hln
    iapply HΦ
    iframe Hp
    have Hc : ¬ (id ∈ s.prs ∧ id = s.cfg.wit ∧ s.cfg.wit ≠ W64 0) := fun h => Hw ⟨h.2.1, h.2.2⟩
    simp only [makeVoterO, if_neg Hc, ownWorkO]
    isplitr; · itrivial
    iapply ownWork_intro chg base cfgp trk (makeVoterM id s) _ prs _ ?_ ?_
      $$ Hcfgp Hc Htrk Hprs Hnew
    · simp only [makeVoterM, ite_eq_left Hmem, flagsOf_insert, Hflags]
    · simp only [makeVoterM, ite_eq_left Hmem]
      exact WitT.set_learner false Hwt Hpv

end proof

end EtcdGrove
end Perennial
