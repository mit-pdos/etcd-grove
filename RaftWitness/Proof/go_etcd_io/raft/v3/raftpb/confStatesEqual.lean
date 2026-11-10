/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/confStatesEqual.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.confStatesEqual
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.idsEqual
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.boolOf
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.uint64Of

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.confStatesEqual.wp_proof
    (wp_idsEqual : raftpb.idsEqual.spec (GF := GF) (hG := hG))
    (wp_boolOf : raftpb.boolOf.spec (GF := GF) (hG := hG))
    (wp_uint64Of : raftpb.uint64Of.spec (GF := GF) (hG := hG)) :
    raftpb.confStatesEqual.spec (GF := GF) (hG := hG) := by
  intro p q dq1 dq2 c1 c2 al1 al2
  wp_start as ⟨H1, H2⟩
  iunfold csPts at H1 H2
  icases H1 with ⟨%sv1, %sl1, %so1, %sn1, %pa1, %pw1, %pwo1, %Hnn1, HV1, Hv1, HL1, Hl1, HO1, Ho1,
    HN1, Hn1, HA1, #cA1, %Hal1, HW1, #cW1, HWO1, #cWO1, #Hpb1⟩
  icases H2 with ⟨%sv2, %sl2, %so2, %sn2, %pa2, %pw2, %pwo2, %Hnn2, HV2, Hv2, HL2, Hl2, HO2, Ho2,
    HN2, Hn2, HA2, #cA2, %Hal2, HW2, #cW2, HWO2, #cWO2, #Hpb2⟩
  -- the result is the conjunction of the five comparisons
  have Hiff : ∀ (r1 r2 r3 r4 r5 : Bool), (r1 = true ↔ c1.Voters' = c2.Voters') →
      (r2 = true ↔ c1.Learners' = c2.Learners') →
      (r3 = true ↔ c1.VotersOutgoing' = c2.VotersOutgoing') →
      (r4 = true ↔ c1.LearnersNext' = c2.LearnersNext') →
      (r5 = true ↔ c1.AutoLeave' = c2.AutoLeave') →
      ((r1 && r2 && r3 && r4 && r5 && decide (c1.Witness' = c2.Witness')) = true ↔ c1 = c2) := by
    intro r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
    cases c1; cases c2
    simp only [Bool.and_eq_true, ConfStateM.mk.injEq, decide_eq_true_eq] at *
    rw [h1, h2, h3, h4, h5]
    simp only [and_assoc]
  -- the end of every path: the result `r`, with the slices given back
  ihave Hfin : iprop(∀ (r : Bool), ⌜r = true ↔ c1 = c2⌝ -∗
      sv1 ↦*{dq1} c1.Voters' -∗ sl1 ↦*{dq1} c1.Learners' -∗ so1 ↦*{dq1} c1.VotersOutgoing' -∗
      sn1 ↦*{dq1} c1.LearnersNext' -∗
      sv2 ↦*{dq2} c2.Voters' -∗ sl2 ↦*{dq2} c2.Learners' -∗ so2 ↦*{dq2} c2.VotersOutgoing' -∗
      sn2 ↦*{dq2} c2.LearnersNext' -∗
      p.[raftpb.ConfState, go!"Voters"] ↦{dq1} sv1 -∗ p.[raftpb.ConfState, go!"Learners"] ↦{dq1} sl1 -∗
      p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq1} so1 -∗
      p.[raftpb.ConfState, go!"LearnersNext"] ↦{dq1} sn1 -∗ p.[raftpb.ConfState, go!"AutoLeave"] ↦{dq1} pa1 -∗
      q.[raftpb.ConfState, go!"Voters"] ↦{dq2} sv2 -∗ q.[raftpb.ConfState, go!"Learners"] ↦{dq2} sl2 -∗
      q.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq2} so2 -∗
      q.[raftpb.ConfState, go!"LearnersNext"] ↦{dq2} sn2 -∗ q.[raftpb.ConfState, go!"AutoLeave"] ↦{dq2} pa2 -∗
      p.[raftpb.ConfState, go!"Witness"] ↦{dq1} pw1 -∗ p.[raftpb.ConfState, go!"WitnessOutgoing"] ↦{dq1} pwo1 -∗
      q.[raftpb.ConfState, go!"Witness"] ↦{dq2} pw2 -∗ q.[raftpb.ConfState, go!"WitnessOutgoing"] ↦{dq2} pwo2 -∗
      Φ #r) $$ [HΦ]
  · iintro %r %Hr Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    iapply HΦ
    iunfold csPts
    isplitl [HV1 Hv1 HL1 Hl1 HO1 Ho1 HN1 Hn1 HA1 HW1 HWO1]
    · iexists sv1, sl1, so1, sn1, pa1, pw1, pwo1
      iframe; iframe cA1 cW1 cWO1 Hpb1
      ipureintro; exact ⟨Hnn1, Hal1⟩
    isplitl
    · iexists sv2, sl2, so2, sn2, pa2, pw2, pwo2
      iframe; iframe cA2 cW2 cWO2 Hpb2
      ipureintro; exact ⟨Hnn2, Hal2⟩
    ipureintro; exact Hr
  wp_auto
  wp_apply wp_idsEqual _ _ _ _ _ _ $$ [$Hv1 $Hv2] as %r1 ⟨Hv1, Hv2, %H1⟩
  cases r1
  · wp_auto
    iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (H1.2 (congrArg ConfStateM.Voters' h)) (by decide))⟩
  wp_auto
  wp_apply wp_idsEqual _ _ _ _ _ _ $$ [$Hl1 $Hl2] as %r2 ⟨Hl1, Hl2, %H2⟩
  cases r2
  · wp_auto
    iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (H2.2 (congrArg ConfStateM.Learners' h)) (by decide))⟩
  wp_auto
  wp_apply wp_idsEqual _ _ _ _ _ _ $$ [$Ho1 $Ho2] as %r3 ⟨Ho1, Ho2, %H3⟩
  cases r3
  · wp_auto
    iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (H3.2 (congrArg ConfStateM.VotersOutgoing' h)) (by decide))⟩
  wp_auto
  wp_apply wp_idsEqual _ _ _ _ _ _ $$ [$Hn1 $Hn2] as %r4 ⟨Hn1, Hn2, %H4⟩
  cases r4
  · wp_auto
    iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (H4.2 (congrArg ConfStateM.LearnersNext' h)) (by decide))⟩
  wp_auto
  wp_apply wp_boolOf _ _ $$ [$cA1]
  wp_apply wp_boolOf _ _ $$ [$cA2]
  by_cases hA : c1.AutoLeave' = c2.AutoLeave'
  · rw [decide_eq_true hA]
    wp_auto
    wp_apply wp_uint64Of _ _ $$ [$cW1]
    wp_apply wp_uint64Of _ _ $$ [$cW2]
    by_cases hW : c1.Witness' = c2.Witness'
    · rw [hW]
      wp_auto
      wp_apply wp_uint64Of _ _ $$ [$cWO1]
      wp_apply wp_uint64Of _ _ $$ [$cWO2]
      iapply Hfin $$ %true [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
      ipureintro
      have h := Hiff true true true true true H1 H2 H3 H4 (by simp [hA])
      simpa [hW] using h
    · rw [show (decide (c1.Witness' = c2.Witness')) = false from decide_eq_false hW]
      wp_auto
      iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
      ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (congrArg ConfStateM.Witness' h) hW)⟩
  · rw [decide_eq_false hA]
    wp_auto
    iapply Hfin $$ %false [] Hv1 Hl1 Ho1 Hn1 Hv2 Hl2 Ho2 Hn2 HV1 HL1 HO1 HN1 HA1 HV2 HL2 HO2 HN2 HA2 HW1 HWO1 HW2 HWO2
    ipureintro; exact ⟨(fun h => nomatch h), (fun h => absurd (congrArg ConfStateM.AutoLeave' h) hA)⟩

end proof

end EtcdGrove
end Perennial
