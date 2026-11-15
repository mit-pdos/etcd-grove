/-
`restartRead.wp_proof` (W4c U5): `ValidSnapshotEntries` (its update committed unchanged, `tInv_dirAu`), the
newest-pair loop (`walNewestPair` of the valid snapshots, through the getters), then at most two attempts:
the oracle with the snapshot's index appended to its opens stored (`tCandOk_addOpen`), `Open` (its raise
committed, `tInv_openAu` over `tCandOk_open`), `ReadAll` (unchanged, `tInv_readAu`, its newest-pair premise
from the history and read position, which no update of the restart moves); on success the read built
(`hsGet`'s getters, `fromRaft` of each entry) and related to an image by `tRead_of_readAll`; on failure
`Close.specFailed`, then `Repair` (unchanged) once. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.restartRead
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.fromRaft
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Open
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReadAll
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseFailed
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Getters
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartAu

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

theorem restartRead.wp_proof
    (wp_vse : ∀ W : WalGS GF, wal.ValidSnapshotEntries.spec (W := W) walRaftMr)
    (wp_open : ∀ W : WalGS GF, go_etcd_io.etcd.server.v3.storage.wal.Open.spec (W := W) walRaftMr)
    (wp_readAll : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.spec (W := W) (walRaftP (GF := GF)) walRaftMr)
    (wp_closeF : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specFailed (W := W) walRaftMr)
    (wp_repair : ∀ W : WalGS GF, wal.Repair.spec (W := W) walRaftMr)
    (wp_getIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF))
    (wp_getTerm : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec (GF := GF))
    (wp_newU64 : newU64.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_fromRaft : fromRaft.spec (GF := GF) (hG := hG)) :
    restartRead.spec (GF := GF) (hG := hG) := by
  intro W e γ lg m v o cd d qp hmn hf hpath hcr hcd hok hlen hrb hroom
  obtain ⟨hia, hnm, hca, hdl⟩ := hpath
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, #Hzap, #Harea, Hpath, Hres, Htok, Hop, Hov, Hrep, Ho,
    Hwo, #Hsl, #Hnm⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  wp_auto
  icases Hdeps with ⟨-, -, -, #Hwpkg, #Hwpbpkg, -, -⟩
  wp_apply (wp_vse W lg e.R e.jr e.area (tWalDir e.area) go!"wal" qp
      (fun od => iprop(⌜od = some d⌝ ∗ tWalOwn γ (some d))) hia hnm hca hdl)
      $$ [Hzap Harea Hpath Hres Hperm Htok Hwo]
    as %sl %err ⟨Hpath, Hres, Hperm, Htok, %od, ⟨%hod, Hwo⟩, Hvs⟩
  · iframe; iframe #
    iapply tInv_dirAu W e γ d
    iframe; iframe #
  subst hod
  cases err with
  | ok ie =>
    wp_auto
    simp only [readFail]
    wp_auto
    iapply HΦ
    iframe
    iexists []
    rw [tWithOpens_nil]
    iframe
    isplitr
    · ipureintro; exact ⟨by simp, rfl, rfl, hok⟩
    rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
    itrivial
  | nil =>
  icases Hvs with (%Herr | ⟨%d0, %ps, %hd0, #Hsl0, #Hps⟩)
  · exact absurd rfl Herr
  cases hd0
  wp_auto
  wp_if_destruct
  · simp only [readFail]
    wp_auto
    iapply HΦ
    iframe
    iexists []
    rw [tWithOpens_nil]
    iframe
    isplitr
    · ipureintro; exact ⟨by simp, rfl, rfl, hok⟩
    rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
    itrivial
  -- the newest valid pair
  have hsl0 : sl.len ≠ W64 0 := Hif
  ihave %hlps := ownSlice_len $$ Hsl0
  iunfold walSnapsAt at Hps
  ihave %hlsn := BigSepL2.bigSepL2_length (PROP := IProp GF) $$ Hps
  ihave HI : (∃ (j : w64) (pr : w64 × w64),
      "i" ∷ i_ptr ↦ j ∗ "idx" ∷ idx_ptr ↦ pr.1 ∗ "term" ∷ term_ptr ↦ pr.2 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        pr = ((walValidSnaps (d.H.map WalOpG.toM) d.cut).take (sint.nat j)).foldl tNewestStep
          (W64 0, W64 0)⌝ : IProp GF) $$ [i idx term]
  · iexists W64 0, (W64 0, W64 0)
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  wp_for HI
  obtain ⟨hj0, hjl, hpr⟩ := Hj
  wp_if_destruct
  · have hjlt : sint.nat j < ps.length := by rw [hlps.1]; word
    obtain ⟨p, hp⟩ : ∃ p, ps[sint.nat j]? = some p := ⟨_, List.getElem?_eq_getElem hjlt⟩
    obtain ⟨s, hs⟩ : ∃ s, (walValidSnaps (d.H.map WalOpG.toM) d.cut)[sint.nat j]? = some s :=
      ⟨_, List.getElem?_eq_getElem (hlsn ▸ hjlt)⟩
    ihave #Hpk := BigSepL2.bigSepL2_lookup (PROP := IProp GF) hp hs $$ Hps
    have hkb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨hj0, Hif⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
    wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p hj0 $$ [Hsl0] as -
    · iframe #; ipureintro; exact hp
    wp_apply wp_getIndex p s $$ [Hpk]
    · iexact Hpk
    try wp_auto
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : (walValidSnaps (d.H.map WalOpG.toM) d.cut).take (sint.nat (j + W64 1)) =
        (walValidSnaps (d.H.map WalOpG.toM) d.cut).take (sint.nat j) ++ [s] := by
      rw [hj1, List.take_succ, hs]; rfl
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
      wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p hj0 $$ [Hsl0] as -
      · iframe #; ipureintro; exact hp
      wp_apply wp_getIndex p s $$ [Hpk]
      · iexact Hpk
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
      wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p hj0 $$ [Hsl0] as -
      · iframe #; ipureintro; exact hp
      wp_apply wp_getTerm p s $$ [Hpk]
      · iexact Hpk
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, s
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, List.foldl_append, ← hpr]
      simp only [List.foldl_cons, List.foldl_nil, tNewestStep]
      rw [if_pos (by word)]
    · try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, pr
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, List.foldl_append, ← hpr]
      simp only [List.foldl_cons, List.foldl_nil, tNewestStep]
      rw [if_neg (by word)]
  -- the loop's exit: the newest valid pair
  have hjn : sint.nat j = (walValidSnaps (d.H.map WalOpG.toM) d.cut).length := by
    rw [← hlsn, hlps.1]; word
  rw [hjn, List.take_length] at hpr
  have hne : walValidSnaps (d.H.map WalOpG.toM) d.cut ≠ [] := by
    intro h
    have h0 : ps.length = 0 := by rw [hlsn, h]; rfl
    apply hsl0
    have := hlps.1
    word
  have hnp : walNewestPair (walValidSnaps (d.H.map WalOpG.toM) d.cut) = some pr := by
    rw [walNewestPair_loop _ hne, hpr]
  try wp_auto
  -- the attempts
  ihave HI2 : (∃ (rep : Bool) (l : List w64) (dc : WalDur) (vc : oracle),
      "repaired" ∷ repaired_ptr ↦ rep ∗ "Hov" ∷ m.[member, go!"o"] ↦ vc ∗
      "Hrep" ∷ oracleRep vc (tWithOpens o l) ∗ "Ho" ∷ tOrOwn γ (tWithOpens o l) none ∗
      "Hwo" ∷ tWalOwn γ (some dc) ∗ "Htok" ∷ WalFs.walUnlockedTok (W := W) ∗
      "Hperm" ∷ osCallPerm (GF := GF) 1 ∗
      "%Hl" ∷ ⌜l.length = (if rep then 1 else 0) ∧ dc.H = d.H ∧ dc.cut = d.cut ∧
        tCandOk (tWithOpens o l) cd dc⌝ : IProp GF) $$ [repaired Hov Hrep Ho Hwo Htok Hperm]
  · iexists false, [], d, v
    rw [tWithOpens_nil]
    simp only [named]
    iframe
    ipureintro; exact ⟨by simp, by simp, by simp, hok⟩
  wp_for HI2
  obtain ⟨hll, hdH, hdcut, hokl⟩ := Hl
  try wp_auto
  simp only [decide_eq_false hmn]
  try wp_auto
  -- `m.o.opens = append(m.o.opens, idx)`, then `storeOracle`
  iunfold oracleRep at Hrep
  icases Hrep with ⟨%Hf, Hcs, #Hsince, Hscap, #Hops, Hopcap⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  wp_apply (wp_slice_append_persistent (V := w64) vc.opens' (tWithOpens o l).opens _ _ (DFrac.own 1))
      $$ [Hops Hopcap Hosl] as %s1 ⟨#Hs1, Hopcap, -⟩
  · iframe; iframe #
  try wp_auto
  have hok1 : tCandOk (tWithOpens o (l ++ [pr.1])) cd dc := by
    rw [← tWithOpens_add]; exact tCandOk_addOpen pr.1 hokl
  have hll2 : l.length ≤ 1 := by rw [hll]; split <;> omega
  have hsm1 : tOrSmall (tWithOpens o (l ++ [pr.1])) := by
    apply tOrSmall_withOpens; simp only [List.length_append, List.length_singleton]; omega
  ihave Hrep1 : oracleRep (oracle.mk vc.created' vc.cands' vc.since' vc.synced' vc.lastHS' s1)
      (tWithOpens o (l ++ [pr.1])) $$ [Hcs Hscap Hopcap]
  · iunfold oracleRep
    simp only [tWithOpens, List.append_assoc] at *
    isplitr
    · ipureintro; exact Hf
    iframe
    isplitl []
    · iexact Hsince
    · iexact Hs1
  ihave #Hrel1 : tRelI (W := W) e.area (tWithOpens o (l ++ [pr.1])) (some dc) $$ []
  · iunfold tRelI
    simp only [show (tWithOpens o (l ++ [pr.1])).created = true from hcr, ↓reduceIte]
    iexists dc, cd
    rw [show tCandMark (tWithOpens o (l ++ [pr.1])) cd = tCandMark o cd from rfl]
    iframe #
    ipureintro; exact ⟨rfl, hcd, hok1⟩
  wp_apply (wp_store W e γ _ (tWithOpens o l) (tWithOpens o (l ++ [pr.1])) (some dc) 1 hf hsm1)
    $$ [Hh Hperm Hrep1 Ho Hwo] as ⟨Hh, Hperm, Hrep1, Ho, Hwo⟩
  · iframe; iframe #
  try wp_auto
  -- `Open(lg, walDir, &walpb.Snapshot{Index: newU64(idx), Term: newU64(term)})`
  wp_apply wp_newU64 as %pi Hpi
  try wp_auto
  wp_apply wp_newU64 as %pt Hpt
  try wp_auto
  imod walSnapIdTerm_lit «$a2_ptr» pi pt _ _ pr.1 pr.2 $$ «$a2» Hpi Hpt with #Hsnap
  have hlen1 : (tCandHist (tWithOpens o l) cd).length < 2 ^ 63 := hlen
  have hok2 : tCandOk (tWithOpens o (l ++ [pr.1])) cd (walOpenRaise pr dc) := by
    rw [← tWithOpens_add]; exact tCandOk_open pr.1 hokl hlen1
  ihave #Hsl1 : WalFs.walSyncedLb (W := W) (tWalDir e.area) (tCandMark (tWithOpens o (l ++ [pr.1])) cd)
    $$ []
  · rw [show tCandMark (tWithOpens o (l ++ [pr.1])) cd = tCandMark o cd from rfl]; iexact Hsl
  wp_apply (wp_open W lg e.R e.jr e.area (tWalDir e.area) go!"wal" «$a2_ptr» pr qp
      (fun od => iprop(⌜od = some dc⌝ ∗ tOrOwn γ (tWithOpens o (l ++ [pr.1])) none ∗
        tWalOwn γ (some (walOpenRaise pr dc)))) hia hnm hca hdl)
      $$ [Hpath Hres Hperm Htok Ho Hwo]
    as %w %err2 ⟨Hpath, Hres, %od, ⟨%hod, Ho, Hwo⟩, Hr⟩
  · iframe; iframe #
    iapply tInv_openAu W e γ (tWithOpens o (l ++ [pr.1])) cd dc pr hcr hcd hok2
    iframe; iframe #
  subst hod
  sorry

end proof

end etcd_wal
end EtcdGrove
end Perennial
