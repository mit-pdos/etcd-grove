/-
`restartRead.wp_proof` (W4c U5): `ValidSnapshotEntries` (its update committed unchanged, `tInv_dirAu`), the
newest-pair loop (`walNewestPair` of the valid snapshots, through the getters), then at most two attempts:
the oracle with the snapshot's index appended to its opens stored (`tCandOk_addOpen`), `Open` (its raise
committed, `tInv_openAu` over `tCandOk_open`), `ReadAll` (unchanged, `tInv_readAu`, its newest-pair premise
from the history and read position, which no update of the restart moves); on success the read built
(`hsGet`'s getters, `fromRaft` of each entry) and related to an image by `tRead_of_readAll`; on failure
`Close.spec` (state `failed`), then `Repair` (unchanged) once. Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.restartRead
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.newU64
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.fromRaft
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Open
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReadAll
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Getters
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartAu

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
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr)
    (wp_repair : ∀ W : WalGS GF, wal.Repair.spec (W := W) walRaftMr)
    (wp_getIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF))
    (wp_getTerm : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec (GF := GF))
    (wp_newU64 : newU64.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_fromRaft : fromRaft.spec (GF := GF) (hG := hG)) :
    restartRead.spec (GF := GF) (hG := hG) := by
  intro W e γ lg m v o cd od qp hmn hf hpath hpf hcd hok hlen hrb hroom
  obtain ⟨hia, hnm, hca, hdl⟩ := hpath
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, #Hzap, #Harea, Hpath, Hres, Htok, Hop, Hov, Hrep, Ho,
    Hwo, #HrW⟩
  iunfold tPerm at Hperm
  icases Hperm with ⟨Hperm, Hor⟩
  icases osPathS_callKey e.R e.area _ e.jr $$ Hpath with ⟨Hpath, %hkc⟩
  have hkw : callKey e.R (tWalDir e.area) = callKey e.R e.area := by rw [tWalDir_child]; exact hkc _
  ihave Hperm := osCallPerm_congr 1 hkw $$ Hperm
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  wp_auto
  icases Hdeps with ⟨-, -, -, #Hwpkg, #Hwpbpkg, -, -⟩
  wp_apply (wp_vse W lg e.R e.jr e.area (tWalDir e.area) go!"wal" qp
      (fun od1 => iprop(⌜od1 = od⌝ ∗ tWalOwn γ od)) 0 hia hnm hca hpf)
      $$ [Hzap Harea Hpath Hres Hperm Htok Hwo]
    as %sl %err ⟨Hpath, Hres, Hperm, Htok, %od1, ⟨%hod, Hwo⟩, Hvs⟩
  · iframe; iframe #
    iapply tInv_dirAu W e γ od
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
    · ipureintro; exact ⟨by simp, tOdRel_refl hok⟩
    rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
    itrivial
  | nil =>
  icases Hvs with (%Herr | ⟨%d, %ps, %hd0, #Hsl0, #Hps⟩)
  · exact absurd rfl Herr
  subst hd0
  have hok := hok d rfl
  have hrb := hrb d rfl
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
    · ipureintro; exact ⟨by simp, Option.Rel.some ⟨rfl, rfl, hok⟩⟩
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
      "Hperm" ∷ osCallPerm (GF := GF) (callKey e.R e.area) 1 ∗
      "Hor" ∷ osCallPerm (GF := GF) (callKey e.R e.orDir) 1 ∗
      "%Hl" ∷ ⌜l.length = (if rep then 1 else 0) ∧ dc.H = d.H ∧ dc.cut = d.cut ∧
        tCandOk (tWithOpens o l) cd dc⌝ : IProp GF) $$ [repaired Hov Hrep Ho Hwo Htok Hperm Hor]
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
  ihave #HrW1 := tRelW_withOpens W e.area o cd (l ++ [pr.1]) $$ HrW
  ihave #Hrel1 := tRelI_of_relW e.area (tWithOpens o (l ++ [pr.1])) cd dc hcd hok1 $$ HrW1
  wp_apply (wp_store W e γ _ (tWithOpens o l) (tWithOpens o (l ++ [pr.1])) (some dc) 1 hf hsm1)
    $$ [Hh Hor Hrep1 Ho Hwo] as ⟨Hh, Hor, Hrep1, Ho, Hwo⟩
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
  wp_apply (wp_open W lg e.R e.jr e.area (tWalDir e.area) go!"wal" «$a2_ptr» pr qp
      (fun od => iprop(⌜od = some dc⌝ ∗ tOrOwn γ (tWithOpens o (l ++ [pr.1])) none ∗
        tWalOwn γ (some (walOpenRaise pr dc)))) 0 hia hnm hca hpf)
      $$ [Hpath Hres Hperm Htok Ho Hwo]
    as %w %err2 ⟨Hpath, Hres, %od, ⟨%hod, Ho, Hwo⟩, Hr⟩
  · iframe; iframe #
    iapply tInv_openAu W e γ (tWithOpens o (l ++ [pr.1])) cd dc pr hcd hok2
    iframe; iframe #
  subst hod
  have hll3 : (l ++ [pr.1]).length ≤ 2 := by simp only [List.length_append, List.length_singleton]; omega
  icases Hr with (⟨%herr, Htok, Hperm⟩ | ⟨%herr, -, Hopening, Hph⟩)
  · cases err2 with
    | nil => exact absurd rfl herr
    | ok ie =>
      wp_auto
      simp only [readFail]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact ⟨hll3, Option.Rel.some ⟨hdH, hdcut, hok2⟩⟩
      rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
      itrivial
  cases err2 with
  | ok ie => cases herr
  | nil =>
  wp_auto
  -- `ReadAll`
  have hnp1 : some pr = walNewestPair (walValidSnaps ((walOpenRaise pr dc).H.map WalOpG.toM)
      (walOpenRaise pr dc).cut) ∧
      walOpenPos ((walOpenRaise pr dc).H.map WalOpG.toM) pr.1 ≤ (walOpenRaise pr dc).unl := by
    refine ⟨by simp only [walOpenRaise, hdH, hdcut]; exact hnp.symm, ?_⟩
    simp only [walOpenRaise]; exact Nat.le_max_right _ _
  wp_apply (wp_readAll W e.R e.jr e.area (tWalDir e.area) go!"wal" w pr qp (1 : Qp).half
      (fun dd => iprop(⌜dd = walOpenRaise pr dc⌝ ∗ tWalOwn γ (some (walOpenRaise pr dc)))) 0 hia hca)
      $$ [Hpath Hph Hopening Hwo]
    as %mdp %hp %esl %err3 ⟨Hpath, Hph, %dd, ⟨%hdd, Hwo⟩, Hr3⟩
  · iframe; iframe #
    iapply tInv_readAu W e γ (walOpenRaise pr dc)
      (fun dd => some pr = walNewestPair (walValidSnaps (dd.H.map WalOpG.toM) dd.cut) ∧
        walOpenPos (dd.H.map WalOpG.toM) pr.1 ≤ dd.unl) hnp1
    iframe; iframe #
  subst hdd
  icases Hr3 with (⟨%herr3, Hfail⟩ | ⟨%herr3, %σ, %esL, %hra, #Hhs, #Hesl, #Hents, -, Hwf, #Hnm2, #Hsl2,
    #Hlen2, Hpw⟩)
  · -- the read failed: `Close`, then `Repair` once
    cases err3 with
    | nil => exact absurd rfl herr3
    | ok ie3 =>
    wp_auto
    wp_apply (wp_closeF W e.R e.jr e.area w (tWalDir e.area) .failed (fun _ => iprop(True))) $$ [Hfail]
      as %errc Hc
    · dsimp only
      iframe; iframe #
      iPkgInit
    cases errc with
    | ok iec =>
      wp_auto
      simp only [readFail]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact ⟨hll3, Option.Rel.some ⟨hdH, hdcut, hok2⟩⟩
      rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
      itrivial
    | nil =>
    icases Hc with (⟨Htok, Hph2⟩ | ⟨%hc, -⟩)
    rotate_left
    · exact absurd rfl hc
    wp_auto
    cases rep
    rotate_left
    · -- already repaired: the read fails
      wp_auto
      simp only [readFail]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact ⟨hll3, Option.Rel.some ⟨hdH, hdcut, hok2⟩⟩
      rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
      itrivial
    wp_auto
    ihave Hph2 := osCallPerm_congr _ hkw $$ Hph2
    ihave Hperm := osCallPerm_halfJoin _ 1 $$ Hph Hph2
    wp_apply (wp_repair W lg e.R e.jr e.area (tWalDir e.area) go!"wal" qp
        (fun od => iprop(⌜od = some (walOpenRaise pr dc)⌝ ∗ tWalOwn γ (some (walOpenRaise pr dc))))
        0 hia hnm hca hpf) $$ [Hpath Hres Hperm Htok Hwo]
      as %b ⟨Hpath, Hres, Hperm, Htok, %od, ⟨%hod, Hwo⟩⟩
    · iframe; iframe #
      iapply tInv_dirAu W e γ (some (walOpenRaise pr dc))
      iframe; iframe #
    cases b
    · -- `Repair` failed: the read fails
      wp_auto
      simp only [readFail]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact ⟨hll3, Option.Rel.some ⟨hdH, hdcut, hok2⟩⟩
      rw [if_neg (by decide : ¬ (W64 1 = W64 0))]
      itrivial
    icases Htok with (Htok | %hb)
    rotate_left
    · cases hb
    wp_auto
    wp_for_post
    iframe
    iexists true, l ++ [pr.1], walOpenRaise pr dc, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨?_, hdH, hdcut, hok2⟩
    simp only [List.length_append, List.length_singleton, ↓reduceIte]
    simp only [Bool.false_eq_true, ↓reduceIte] at hll
    omega
  -- the read succeeded
  cases err3 with
  | ok ie3 => cases herr3
  | nil =>
  wp_auto
  ihave #Hhg := walHsIn_hsGet $$ Hhs
  dsimp only
  try wp_auto
  wp_apply (wp_hsGetTerm hp σ.hs) $$ [Hhg]
  · iexact Hhg
  try wp_auto
  wp_apply (wp_hsGetVote hp σ.hs) $$ [Hhg]
  · iexact Hhg
  try wp_auto
  wp_apply (wp_hsGetCommit hp σ.hs) $$ [Hhg]
  · iexact Hhg
  try wp_auto
  -- the entries, read back
  wp_apply (wp_slice_make2 (V := entry) (W64 0)) as %rs0 ⟨Hrs, Hrcap⟩
  · ipureintro; decide
  try wp_auto
  ihave %hlesl := ownSlice_len $$ Hesl
  iunfold walEntsIn at Hents
  ihave %hlents := BigSepL2.bigSepL2_length (PROP := IProp GF) $$ Hents
  ihave HI3 : (∃ (j : w64) (rs : GoSlice),
      "i" ∷ i_ptr ↦ j ∗
      "c" ∷ c_ptr ↦ (contents.mk ⟨σ.hs.Term', σ.hs.Vote', σ.hs.Commit'⟩ pr.1 pr.2 rs) ∗
      "Hrs" ∷ rs ↦* ((σ.ents.take (sint.nat j)).map tFromRaft) ∗
      "Hrcap" ∷ ownSliceCap entry rs (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z esl.len⌝ : IProp GF) $$ [i c Hrs Hrcap]
  · iexists W64 0, rs0
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil,
      List.replicate_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for HI3
  obtain ⟨hj0, hjl⟩ := Hj
  wp_if_destruct
  · have hjlt : sint.nat j < esL.length := by rw [hlesl.1]; word
    obtain ⟨re, hre⟩ : ∃ re, esL[sint.nat j]? = some re := ⟨_, List.getElem?_eq_getElem hjlt⟩
    obtain ⟨me, hme⟩ : ∃ me, σ.ents[sint.nat j]? = some me :=
      ⟨_, List.getElem?_eq_getElem (hlents ▸ hjlt)⟩
    ihave #Hre := BigSepL2.bigSepL2_lookup (PROP := IProp GF) hre hme $$ Hents
    have hkb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z esl.len := ⟨hj0, Hif⟩
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
    wp_apply wp_load_slice_index esl (sint.Z j) esL DFrac.discard re hj0 $$ [Hesl] as -
    · iframe #; ipureintro; exact hre
    wp_apply (wp_fromRaft re me) $$ [Hre]
    · iframe #
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    try wp_auto
    wp_apply (wp_slice_append (V := entry) rs _ _ _ (DFrac.own 1)) $$ [Hrs Hrcap Hosl]
      as %rs' ⟨Hrs, Hrcap, -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, rs'
    simp only [named]
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hj1, List.take_add_one, hme]
    simp only [Option.toList, List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  -- the read's result
  have hjn : sint.nat j = σ.ents.length := by rw [← hlents, hlesl.1]; word
  rw [hjn, List.take_length]
  ipersist Hrs
  try wp_auto
  simp only [readOK]
  try wp_auto
  wp_for_post
  ihave Hph : tPerm (GF := GF) e (1 : Qp).half $$ [Hph Hor]
  · iunfold tPerm; rw [hkw]; iframe
  iapply HΦ
  have hH1 : (walOpenRaise pr dc).H = d.H := hdH
  have hra' : WalEnc.walReadAllOk (d.H.map WalOpG.toM) (walOpenRaise pr dc).cut pr σ := by
    rw [← hH1]; exact hra
  have hrb' : WalEnc.walReadsBack ((walOpenRaise pr dc).H.map WalOpG.toM) := by
    rw [hH1]; exact hrb _ _ _ hra'
  obtain ⟨img, himg, hI, hR⟩ := tRead_of_readAll (c := ⟨⟨σ.hs.Term', σ.hs.Vote', σ.hs.Commit'⟩, pr.1, pr.2,
      σ.ents.map tFromRaft⟩) hok2 hra hrb' rfl rfl rfl rfl
  rw [hH1] at hI
  iframe
  isplitr
  · ipureintro; exact ⟨hll3, Option.Rel.some ⟨hdH, hdcut, hok2⟩⟩
  simp only [↓reduceIte]
  rw [hH1] at *
  iframe
  iexists ⟨⟨σ.hs.Term', σ.hs.Vote', σ.hs.Commit'⟩, pr.1, pr.2, σ.ents.map tFromRaft⟩, d
  iframe #
  isplitr
  · ipureintro; rfl
  isplitl []
  · iunfold contentsRep
    iframe #
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  ipureintro
  exact ⟨img, himg, hI, hR⟩

end proof

end etcd_wal
end EtcdGrove
end Perennial
