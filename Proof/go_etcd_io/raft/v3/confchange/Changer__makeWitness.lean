/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__makeWitness.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeWitness
public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.incoming
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

theorem confchange.Changer.makeWitness.wp_proof
    (wp_Changer_initProgress : confchange.Changer.initProgress.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_fmt_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    confchange.Changer.makeWitness.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg base s id dq Hid0 Hmi
  wp_start as ⟨Hp, Hw⟩
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg, %prs, %pvs, Hcfgp, Hc, Htrk, Hprs, %Hflags, %Hwt, Hnew⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `if cfg.Witnesses[0] > 0 && cfg.Witnesses[0] != id`
  icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn⟩
  iStructNamed Hcfgp
  icases array_acc _ (sint.Z (W64 0)) _ _ _ s.cfg.wit (by decide) (by rw [Hwit.1]; rfl)
    $$ Witnesses with ⟨Hw0, Hwback⟩
  wp_auto
  by_cases Hother : s.cfg.wit ≠ W64 0 ∧ s.cfg.wit ≠ id
  · -- another witness: "cannot have more than one witness in incoming"
    have Hgt : decide (uint.Z (W64 0) < uint.Z s.cfg.wit) = true := by
      apply decide_eq_true
      have : uint.Z s.cfg.wit ≠ 0 := fun h => Hother.1 (by word)
      word
    rw [Hgt]
    wp_auto
    rw [decide_eq_false (fun h => Hother.2 h)]
    wp_auto
    ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
    wp_apply wp_fmt_Errorf $$ [$Hnil] as %e -
    · fmt_args_ok
    iapply HΦ
    iframe Hp
    simp only [makeWitnessM, if_pos Hother, ownWorkO]
    ipureintro; intro h; cases h
  have Hwid : s.cfg.wit = W64 0 ∨ s.cfg.wit = id := by
    by_cases h0 : s.cfg.wit = W64 0
    · exact .inl h0
    · exact .inr (Classical.byContradiction fun h => Hother ⟨h0, h⟩)
  -- the test is false
  have Hgt0 : decide (uint.Z (W64 0) < uint.Z s.cfg.wit) = decide (s.cfg.wit ≠ W64 0) := by
    apply decide_eq_decide.2; constructor
    · intro hl he; rw [he] at hl; exact absurd hl (by decide)
    · intro hne; have : uint.Z s.cfg.wit ≠ 0 := fun h' => hne (by word)
      word
  rw [Hgt0]
  by_cases h0 : s.cfg.wit = W64 0
  rw [decide_eq_false (fun hne => hne h0)]
  rotate_left
  rw [decide_eq_true h0]
  wp_auto
  rw [decide_eq_true (Hwid.resolve_left h0)]
  all_goals
    wp_auto
    ihave Witnesses := Hwback $$ Hw0
    rw [list_set_lookup_self _ _ _ (show cfg.Witnesses'.arr[(sint.Z (W64 0)).toNat]? = some s.cfg.wit by
      rw [Hwit.1]; rfl)]
    ihave Hcfgp : (cfgp ↦ (cfg : tracker.Config)) $$ [Voters AutoLeave Learners LearnersNext Witnesses]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    -- `pr := trk[id]`
    wp_apply wp_map_lookup1 $$ Htrk as Htrk
    rcases Hlk : prs !! id with _ | pr
    · -- a new id: `initProgress(..., false, true)`
      simp only [Option.getD_none]
      wp_auto
      have Hid : id ∉ s.prs := by
        rw [← Hflags, flagsOf_mem]
        intro h; rw [← Hdom, Hlk] at h; cases h
      have Hw0 : s.cfg.wit = W64 0 := by
        rcases Hwid with h | h
        · exact h
        · exfalso; apply Hid
          have := Hwt.1 (by rw [h]; exact Hid0)
          rw [← h, ← Hflags, flagsOf_mem]; exact this
      ihave Hc := ownCfgCC_intro cfg (DFrac.own 1) s.cfg vin vout Harr Hal Hwit $$ Hin Hout Hl Hln
      ihave Hw := ownWork_intro chg base cfgp trk s cfg prs pvs Hflags Hwt $$ Hcfgp Hc Htrk Hprs Hnew
      wp_apply wp_Changer_initProgress c_ptr cfgp trk chg base s id false true _ Hid
        (fun _ => ⟨rfl, Hid0, Hw0⟩) Hmi
        $$ [$c $Hw] as ⟨c, Hw⟩
      iapply HΦ
      iframe Hp
      simp only [makeWitnessM, if_neg Hother, if_pos Hid, ownWorkO]
      isplitr; · itrivial
      iexact Hw
    · -- a tracked id: the witness is re-added, any other is an error
      simp only [Option.getD_some]
      obtain ⟨pv, Hpv⟩ : ∃ pv, pvs !! id = some pv :=
        Option.isSome_iff_exists.1 ((Hdom id).1 (by rw [Hlk]; rfl))
      have Hmem : id ∈ s.prs := by
        rw [← Hflags, flagsOf_mem, Hpv]; rfl
      have Hnm : ¬ (id ∉ s.prs) := fun h => h Hmem
      icases (BigSepM2.bigSepM2_delete Hlk Hpv).1 $$ Hprs with ⟨Hpr, Hprs⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %Hprnn⟩
      wp_if_destruct
      · exact absurd rfl Hprnn
      have Hpvw := Hwt.2 id pv Hpv
      by_cases Hiw : id = s.cfg.wit
      · rw [show (#(!pv.IsWitness') : val) = #false by rw [Hpvw, decide_eq_true ⟨Hiw, fun h => Hid0 (Hiw.trans h)⟩]; rfl]
        wp_auto
        ihave Hprs := (BigSepM2.bigSepM2_delete (PROP := IProp GF)
        (Φ := fun (_ : w64) (pr : Loc) (pv : tracker.Progress) => iprop(pr ↦ pv)) Hlk Hpv).2 $$ [$Hpr $Hprs]
        -- `incoming(cfg.Voters)[id] = struct{}{}`, `cfg.Witnesses[0] = id` (unchanged)
        wp_apply wp_confchange_incoming _ vin vout Harr
        wp_apply wp_mapInsert $$ Hin as Hin
        icases typedPointsto_not_null_dup _ _ _ $$ Hcfgp with ⟨Hcfgp, %Hcnn'⟩
        iStructNamed Hcfgp
        icases array_acc _ (sint.Z (W64 0)) _ _ _ s.cfg.wit (by decide) (by rw [Hwit.1]; rfl)
          $$ Witnesses with ⟨Hw0, Hwback⟩
        wp_auto
        ihave Witnesses := Hwback $$ Hw0
        rw [list_set_lookup_self _ _ _ (show cfg.Witnesses'.arr[(sint.Z (W64 0)).toNat]? = some id by
          rw [Hwit.1, ← Hiw]; rfl)]
        ihave Hcfgp : (cfgp ↦ (cfg : tracker.Config)) $$ [Voters AutoLeave Learners LearnersNext Witnesses]
        · iapply typedPointsto_combine _ _ _ Hcnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        iapply HΦ
        iframe Hp
        simp only [makeWitnessM, if_neg Hother, if_neg Hnm, if_pos Hiw, ownWorkO]
        isplitr; · itrivial
        iapply ownWork_intro chg base cfgp trk ⟨{ s.cfg with incoming := <[id := ()]> s.cfg.incoming }, s.prs⟩
          cfg prs pvs Hflags Hwt $$ Hcfgp [Hin Hout Hl Hln] Htrk Hprs Hnew
        iapply ownCfgCC_intro cfg (DFrac.own 1) { s.cfg with incoming := <[id := ()]> s.cfg.incoming }
          vin vout Harr Hal
          ⟨Hwit.1, fun h => (gset_mem_insert _ _ _).2 (.inr (Hwit.2 h))⟩ $$ Hin Hout Hl Hln
      · rw [show (#(!pv.IsWitness') : val) = #true by rw [Hpvw, decide_eq_false (fun h => Hiw h.1)]; rfl]
        wp_auto
        ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
        wp_apply wp_fmt_Errorf $$ [$Hnil] as %e -
        · fmt_args_ok
        iapply HΦ
        iframe Hp
        simp only [makeWitnessM, if_neg Hother, if_neg Hnm, if_neg Hiw, ownWorkO]
        ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
