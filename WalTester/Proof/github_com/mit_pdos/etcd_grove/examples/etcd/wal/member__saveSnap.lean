/-
`member.saveSnap.wp_proof` (W4c U5): the snapshot operation appended to `since` and stored (`tRelI_snap1`),
`SaveSnapshot` of the literal (`walSnapAt_litCs`: raft's canonical conf state since 2026-11-15) with its
update committed on the tester's invariant (`tInv_snapAu`), then the mark moved and stored. Lean-first (no
Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__saveSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapAu

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem member.saveSnap.wp_proof
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_newU64 : newU64.spec (GF := GF) (hG := hG))
    (wp_SaveSnapshot : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr) :
    member.saveSnap.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc idx term hf hok hhs hi ht hsm1 hsim hcwf
  wp_start as Hres
  iunfold memSaveRes at Hres
  icases Hres with ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hpath, Hw, Hov, Hrep, Ho, Hwo, #Harea, Hwf,
    #Hnm, #Hsl, #Hll⟩
  try wp_auto
  -- `m.o.since = append(m.o.since, walOp{snap: true, idx: idx, term: term})`
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hf, Hcs, #Hsince, Hscap, #Hop, Hopcap⟩
  iunfold opsRep at Hsince
  icases Hsince with ⟨%vs, #Hs, #Hel⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  wp_apply (wp_slice_append_persistent (V := walOp) v.since' vs _ _ (DFrac.own 1)) $$ [Hs Hscap Hosl]
    as %s1 ⟨#Hs1, Hscap, -⟩
  · iframe; iframe #
  try wp_auto
  ihave Hnil : (slice.nil : GoSlice) ↦* ([] : List TEnt) $$ []
  · iapply ownSlice_nil
  ipersist Hnil
  ihave Hrep1 : oracleRep (oracle.mk v.created' v.cands' s1 v.synced' v.lastHS' v.opens')
      (tSnapO1 o idx term) $$ [Hcs Hscap Hopcap]
  · iunfold oracleRep
    simp only [tSnapO1]
    isplitr
    · ipureintro; exact Hf
    iframe
    isplitl []
    · iunfold opsRep
      iexists _
      iframe Hs1
      iapply opsElems_snoc
      iframe Hel
      unfold opRep tSnapOp
      iframe Hnil
      ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    · iexact Hop
  ihave #Hrel := tRelI_snap1 W e.area o c d idx term hok.1 hok.2.1 (tCandOk_snap1 hok hi ht hsim)
    (tCheckWf_snapO1 hcwf hi ht hsm1)
    $$ [Hsl Hnm]
  · isplitl []
    · iexact Hsl
    · iexact Hnm
  iunfold tPerm at Hperm
  icases Hperm with ⟨Hpw_, Hperm⟩
  wp_apply (wp_store W e γ _ os (tSnapO1 o idx term) (some d) 1 hf hsm1) $$ [Hh Hperm Hrep1 Ho Hwo]
    as ⟨Hh, Hperm, Hrep1, Ho, Hwo⟩
  · iframe; iframe #
  ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
  · iunfold tPerm; iframe
  try wp_auto
  -- the literal
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %svl ⟨Hsv, -⟩
  try wp_auto
  wp_apply wp_newU64 as %pi Hpi
  try wp_auto
  wp_apply wp_newU64 as %pt Hpt
  try wp_auto
  imod walSnapAt_litCs «$a0_ptr» pi pt «$r0_ptr» «$v1_ptr» _ _ _ _ _ idx term $$ «$a0» Hpi Hpt «$r0» Hsv
    «$v1» with #Hsnap
  ihave Hau := tInv_snapAu W e γ o c d idx term hok hi ht hsim $$ [Hwo Ho]
  · iframe; iframe #
  -- the member's handle, shared for the call (the tester assumes nothing of I/O errors: `ioNone`) and taken back after it
  iapply fupd_wp
  imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [Hwf]
    with ⟨%γs, Hws, %hγ0⟩
  · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ Hwf
  rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
  let γs : WalShN := ⟨γs1, γs2, 0⟩
  imodintro
  wp_apply (lc := 1) (wp_SaveSnapshot W e.R e.jr e.area w (tWalDir e.area) (.shared γs 1) «$a0_ptr»
      (absSnapMd idx term) true true _) $$ [Hws Hau]
    as %err Hr
  · dsimp only
    iframe; iframe #
    ipureintro
    refine ⟨Or.inr rfl, fun hc => absurd hc walCov_ioNone, Or.inr rfl, ?_, absSnapMd_enc_lt idx term⟩
    show uint.nat idx < 2 ^ 64 - 1
    omega
  icases Hr with (⟨%Herr, Hws, %d0, ⟨%hd0, Hwo, Ho⟩, #Hlen1, #Hsy⟩ | ⟨%Herr, %d0, ⟨%hd0, Hwo, Ho⟩⟩)
  · subst Herr
    iapply fupd_wp
    imod walOpenWS_reclaim (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) γs $$ [Hws Hlc1]
      with Hwf
    · iframe Hws Hlc1
    imodintro
    ihave Hwf := walHdl_wf (W := W) ioNone _ _ _ _ $$ Hwf
    subst d0
    try wp_auto
    have hd' := tMemOk_snap1 hok hi ht hsim
    ihave ⟨%hl, Hrep1⟩ := oracleRep_synced _ _ $$ Hrep1
    ihave #Hrel2 := tRelI_synced W e.area (tSnapO1 o idx term) c (tSnapD d idx term) hd' hl
      (tCheckWf_snapO1 hcwf hi ht hsm1) $$ [Hsy Hnm]
    · isplitl []
      · rw [show (tSnapD d idx term).H.length = d.H.length + 1 by simp [tSnapD]]; iexact Hsy
      · iexact Hnm
    have hsm2 : tOrSmall (tSnapO o idx term) := by
      unfold tOrSmall at *; rw [tEncodeOracle_snapO]; rw [tEncodeOracle_snapO1] at hsm1; exact hsm1
    iunfold tPerm at Hperm
    icases Hperm with ⟨Hpw_, Hperm⟩
    wp_apply (wp_store W e γ _ (tSnapO1 o idx term) (tSnapO o idx term) (some (tSnapD d idx term))
        1 hf hsm2) $$ [Hh Hperm Hrep1 Ho Hwo]
      as ⟨Hh, Hperm, Hrep1, Ho, Hwo⟩
    · iframe; iframe #; unfold tSnapO; iexact Hrel2
    ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
    · iunfold tPerm; iframe
    try wp_auto
    iapply HΦ
    iunfold memOpPost
    iframe Hh Hperm Hpath Hw
    iexists _
    iframe Hov
    isplitl [Ho]
    · iexists _; iexact Ho
    simp only [↓reduceIte]
    iexists tSnapD d idx term
    iframe Hwo Hwf Hrep1
    isplitr
    · ipureintro; exact ⟨tMemOk_synced (o := tSnapO1 o idx term) hd' hl, tMemHs_snap hhs idx term⟩
    have hcm2 : tCandMark (tSnapO o idx term) c = d.H.length + 1 := by
      show tCandMark (tSynced (tSnapO1 o idx term)) c = _
      rw [tSynced_mark _ c hl, ← tMemOk_len hd']; simp [tSnapD]
    rw [hcm2]
    isplitl []
    · iexact Hsy
    rw [show (tSnapD d idx term).H.length = d.H.length + 1 by simp [tSnapD]]
    iexact Hlen1
  · cases err with
    | nil => exact absurd rfl Herr.1
    | ok ie =>
    try wp_auto
    iapply HΦ
    iunfold memOpPost
    iframe Hh Hperm Hpath Hw
    iexists _
    iframe Hov
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl [Ho]
    · iexists _; iexact Ho
    ipureintro; trivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
