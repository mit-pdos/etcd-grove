/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__Simple.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.Changer__checkAndCopy
public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__err
public import Spec.go_etcd_io.raft.v3.confchange.Changer__apply
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.confchange.symdiff
public import Spec.go_etcd_io.raft.v3.confchange.checkAndReturn

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

theorem confchange.Changer.Simple.wp_proof
    (wp_Changer_checkAndCopy : confchange.Changer.checkAndCopy.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_Changer_err : confchange.Changer.err.spec (GF := GF) (hG := hG))
    (wp_Changer_apply : confchange.Changer.apply.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_symdiff : confchange.symdiff.spec (GF := GF) (hG := hG))
    (wp_confchange_checkAndReturn : confchange.checkAndReturn.spec (GF := GF) (hG := hG)) :
    confchange.Changer.Simple.spec (GF := GF) (hG := hG) := by
  intro p chg c prs pvs ccs l dq dqs dqc dqm dqp Hmi
  wp_start as ⟨Hp, Hccs, Htc⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `cfg, trk, err := c.checkAndCopy()`
  wp_apply wp_Changer_checkAndCopy c_ptr chg c prs pvs _ dqc dqm dqp $$ [$c $Htc]
    as %cfg' %trk %err ⟨c, Htc, Hres⟩
  icases Hres with (⟨%Hninv, %Herr⟩ | ⟨⟨%Hinv, %Herr⟩, Hc', ⟨%prs', Htrk, Hcopies⟩⟩)
  · -- the tracker fails `checkInvariants`
    cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      wp_auto
      wp_apply wp_Changer_err $$ [$c] as %cfg0 c
      iapply HΦ
      iframe
      simp only [simpleM, if_pos Hninv, ownResult]
      ipureintro; intro h; cases h
  subst Herr
  wp_auto
  have Hs0 : ¬ ¬ CfgInv (clearAutoLeave { cfg := c, prs := flagsOf pvs }) := fun h => h Hinv
  icases ownCfgCC_elim _ _ _ $$ Hc' with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
  wp_apply wp_confchange_joint _ vin vout _ _ Harr $$ [$Hout] as Hout
  wp_if_destruct
  · -- joint: "can't apply simple config change in joint config"
    have Hj : c.outgoing ≠ ∅ := by
      intro h; rw [h, GMap.map_size_empty] at Hif; exact absurd Hif (by decide)
    wp_apply errors.wp_New as %e #He
    wp_apply wp_Changer_err $$ [$c] as %cfg0 c
    iapply HΦ
    iframe
    simp only [simpleM, if_neg Hs0, if_pos Hj, ownResult]
    ipureintro; intro h; cases h
  have Hj : ¬ c.outgoing ≠ ∅ := fun h => Hif (by
    rcases Nat.eq_zero_or_pos (GMap.size c.outgoing) with h0 | h0
    · exact absurd (GMap.map_size_empty_inv _ h0) h
    · exact h0)
  -- `c.apply(&cfg, trk, ccs...)` on the copies
  ihave Hout := ownIdsetC_join _ _ _ Hcout $$ Hout
  ihave Hc' : ownCfgCC cfg' (DFrac.own 1) (clearAutoLeave { cfg := c, prs := flagsOf pvs }).cfg
    $$ [Hin Hout Hl Hln]
  · iapply ownCfgCC_intro cfg' (DFrac.own 1) (clearAutoLeave { cfg := c, prs := flagsOf pvs }).cfg
      vin vout Harr (by simpa using Hal) $$ [Hin] [Hout] [Hl] [Hln]
    all_goals simp only [clearAutoLeave.proj_cfg]
    · iexact Hin
    · iexact Hout
    · iexact Hl
    · iexact Hln
  ihave Hnew := ownNewPr_copies (GF := GF) chg pvs
  ihave Hw := ownWork_intro chg pvs cfg_ptr trk (clearAutoLeave { cfg := c, prs := flagsOf pvs })
    cfg' prs' pvs rfl $$ cfg Hc' Htrk Hcopies Hnew
  wp_apply wp_Changer_apply c_ptr cfg_ptr trk chg pvs _ ccs l _ _ Hmi $$ [$c $Hccs $Hw]
    as %err2 ⟨c, Hccs, Hres⟩
  rcases Happ : applyM l (clearAutoLeave { cfg := c, prs := flagsOf pvs }) with _ | s1
  · -- `apply` fails
    icases Hres with %Herr2
    cases err2 with
    | nil => exact absurd rfl Herr2
    | ok e =>
      wp_auto
      wp_apply wp_Changer_err $$ [$c] as %cfg0 c
      iapply HΦ
      iframe
      simp only [simpleM, if_neg Hs0, if_neg Hj, Happ, ownResult]
      ipureintro; intro h; cases h
  icases Hres with ⟨%Herr2, Hw⟩
  subst Herr2
  wp_auto
  -- `symdiff(incoming(c.Tracker.Voters), incoming(cfg.Voters))`
  unfold ownTrackerCC
  icases Htc with ⟨Htcc, Hpm, Hprs⟩
  icases ownCfgCC_elim _ _ _ $$ Htcc with ⟨%vin0, %vout0, %Harr0, Hin0, Hout0, Hl0, Hln0, %Hal0⟩
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg1, %prs1, %pvs1, Hcfgp, Hc1, Htrk, Hprs1, %Hflags1, Hnew1⟩
  icases ownCfgCC_elim _ _ _ $$ Hc1 with ⟨%vin1, %vout1, %Harr1, Hin1, Hout1, Hl1, Hln1, %Hal1⟩
  wp_apply wp_confchange_incoming _ vin0 vout0 Harr0
  wp_apply wp_confchange_incoming _ vin1 vout1 Harr1
  wp_apply wp_confchange_symdiff $$ [$Hin0 $Hin1] as ⟨Hin0, Hin1⟩
  ihave Htcc := ownCfgCC_intro _ dqc c vin0 vout0 Harr0 Hal0 $$ Hin0 Hout0 Hl0 Hln0
  ihave Hc1 := ownCfgCC_intro cfg1 (DFrac.own 1) s1.cfg vin1 vout1 Harr1 Hal1 $$ Hin1 Hout1 Hl1 Hln1
  wp_if_destruct
  · -- "more than one voter changed without entering joint config"
    wp_apply errors.wp_New as %e #He
    iapply HΦ
    iframe
    have Hbig : SymdiffTooBig c.incoming s1.cfg.incoming := by
      unfold SymdiffTooBig; simpa using Hif
    simp only [simpleM, if_neg Hs0, if_neg Hj, Happ, if_pos Hbig, ownResult]
    ipureintro; intro h; cases h
  have Hbig : ¬ SymdiffTooBig c.incoming s1.cfg.incoming := by
    unfold SymdiffTooBig; simpa using Hif
  -- `checkAndReturn(cfg, trk)`
  wp_apply wp_confchange_checkAndReturn _ _ _ _ _ _ _ _ $$ [$Hc1 $Htrk $Hprs1]
    as %cfg2 %trk2 %err3 ⟨Hc1, Htrk, Hprs1, %Hres3⟩
  iapply HΦ
  iframe
  simp only [simpleM, if_neg Hs0, if_neg Hj, Happ, if_neg Hbig, checkedM]
  rw [Hflags1] at Hres3
  rcases Hres3 with ⟨Hinv3, Herr3, rfl, rfl⟩ | ⟨Hinv3, Herr3⟩
  · simp only [if_pos Hinv3, ownResult]
    iframe
    isplitr
    · ipureintro; exact Herr3
    unfold ownPrsW
    iexists prs1, pvs1
    simp only [named]
    iframe
    ipureintro; exact Hflags1
  · simp only [if_neg Hinv3, ownResult]
    ipureintro; exact Herr3

end proof

end EtcdGrove
end Perennial
