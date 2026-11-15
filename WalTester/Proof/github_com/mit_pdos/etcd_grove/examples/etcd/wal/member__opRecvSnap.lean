/- Lean-first (no Rocq counterpart). The proof of `member.opRecvSnap`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opRecvSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__saveSnap
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__next
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__size
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__hs
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync

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

set_option maxHeartbeats 1000000 in
theorem member.opRecvSnap.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_next : rnd.next.spec (GF := GF) (hG := hG)) (wp_size : member.size.spec (GF := GF) (hG := hG))
    (wp_hs : member.hs.spec (GF := GF) (hG := hG)) (wp_save : member.save.spec (GF := GF) (hG := hG))
    (wp_saveSnap : member.saveSnap.spec (GF := GF) (hG := hG))
    (wp_sync : member.sync.spec (GF := GF) (hG := hG)) :
    member.opRecvSnap.spec (GF := GF) (hG := hG) := by
  intro W e γ m qc o hf hroom
  wp_start as Hlive
  iunfold memLive at Hlive
  icases Hlive with ⟨%w, %v, %os, %c, %d, %t, %vo, %cm, %bs, %l, %tm, %M, %r, %rv, Hres, Ht, Hv, Hc, Hb,
    Hl, Htm, HM, Hr, Hrv, Hpw, %Hfacts⟩
  obtain ⟨hok, hhs, hfl, hwf⟩ := Hfacts
  wp_auto
  wp_if_destruct
  · iapply HΦ
    simp only [↓reduceIte]
    iexists o
    isplitl
    · iunfold memLive
      iexists w, v, os, c, d, t, vo, cm, bs, l, tm, M, r, rv
      iframe
      ipureintro; exact ⟨hok, hhs, hfl, hwf⟩
    · ipureintro; omega
  wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv1, Hrv⟩, %hk⟩
  rw [if_neg (by decide)] at hk
  ihave ⟨Hres, #Hpers⟩ := memSaveRes_pers W e γ m w v o os c d qc $$ Hres
  have hs63 : uint.nat (l + W64 1 + k) < 2 ^ 63 := by word
  wp_apply (wp_saveSnap W e γ m w v o os c d qc (l + W64 1 + k) t hf hok hhs hs63 hfl.1
    (tOrRoom_snap hroom (by omega) _ _)) $$ [$Hres] as %b1 Hpost1
  cases b1
  · try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  try wp_auto
  ihave Hres1 := memSaveRes_postOp W e γ m w _ c qc $$ [$Hpers $Hpost1]
  icases Hres1 with ⟨%v1, %os1, %d1, Hres1, %Hok1⟩
  wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %mp Hmp
  wp_apply (wp_mapInsert go.uint64 mp _ (l + W64 1 + k) t) $$ [$Hmp] as Hmp
  wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %esl0 ⟨Hesl0, Hcap0⟩
  · ipureintro; word
  simp only [List.replicate_zero]
  try wp_auto
  wp_apply wp_choose $$ [$Hrv] as %kk ⟨⟨%rv2, Hrv⟩, %hkk⟩
  rw [if_neg (by decide)] at hkk
  try wp_auto
  have hkk2 : uint.nat kk ≤ 2 := by word
  ihave HI : (∃ (i : w64) (esl : GoSlice) (es : List TEnt) (M' : GMap w64 w64) (l' : w64) (rvx : rnd),
      "i" ∷ i_ptr ↦ i ∗ "es" ∷ es_ptr ↦ esl ∗ "Hes" ∷ esl ↦* es ∗
      "Hcap" ∷ ownSliceCap TEnt esl (DFrac.own 1) ∗ "Hmp" ∷ mp ↦$ M' ∗
      "Hl" ∷ m.[member, go!"last"] ↦ l' ∗ "Hrv" ∷ r ↦ rvx ∗
      "%Hi" ∷ ⌜uint.nat (l + W64 1 + k) + 1 ≤ uint.nat i ∧
        uint.nat i ≤ uint.nat (l + W64 1 + k) + uint.nat kk + 1 ∧
        es.length = uint.nat i - (uint.nat (l + W64 1 + k) + 1) ∧ (∀ x ∈ es, tEntWf x) ∧
        tTermsFrom t ∅ M'⌝ : IProp GF) $$ [i es Hesl0 Hcap0 Hmp Hl Hrv]
  · iexists _, esl0, [], _, _, rv2
    iframe
    ipureintro
    refine ⟨by word, by word, by simp only [List.length_nil]; word, by simp, tTermsFrom_insert (tTermsFrom_refl t ∅) _⟩
  wp_for HI
  by_cases hle : uint.Z i ≤ uint.Z (l + W64 1 + k + kk)
  · simp only [hle, _root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply (wp_size m r rvx) $$ [$Hr $Hrv] as %sz ⟨Hr, ⟨%rvy, Hrv⟩, %hsz⟩
    wp_apply (wp_next r rvy) $$ [$Hrv] as %x ⟨%rvz, Hrv⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_apply wp_slice_append $$ [$Hes $Hcap $Hosl] as %esl2 ⟨Hes2, Hcap2, -⟩
    wp_apply (wp_mapInsert go.uint64 mp M' i t) $$ [$Hmp] as Hmp
    wp_for_post
    iframe
    iexists i + W64 1, esl2, es ++ [entry.mk i t sz x], <[i := t]> M', i, rvz
    iframe
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hi
    have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    refine ⟨by omega, by word, by simp only [List.length_append, List.length_singleton]; omega, ?_,
      tTermsFrom_insert h5 i⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact h4 y hy
    · simp only [List.mem_singleton] at hy
      subst hy
      exact ⟨by simp; omega, by simp; omega, by simp; word, by simpa using hfl.1⟩
  · simp only [hle, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte, val_false_ne_true,
      not_false_eq_true]
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hi
    have hesl : es.length ≤ 2 := by
      have : uint.nat i = uint.nat (l + W64 1 + k) + uint.nat kk + 1 := by word
      omega
    wp_auto
    have hsnap : tOrSmall (tSnapO1 o (l + W64 1 + k) t) := tOrRoom_snap hroom (by omega) _ _
    have hroom1 : tOrRoom (tSnapO o (l + W64 1 + k) t) 120 := tOrRoom_snapO (n := 120) hroom _ _
    have hsv := tOrRoom_save hroom1 (es := es) (by omega) (hardState.mk t vo (l + W64 1 + k))
    wp_apply (wp_hs m t vo (l + W64 1 + k)) $$ [$Ht $Hv $Hc] as ⟨Ht, Hv, Hc⟩
    imod ownSlice_persist $$ Hes with #Hes
    try wp_auto
    iunfold memSaveRes at Hres1
    icases Hres1 with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, H10, H11, H12, #H13, H14, #H15, #H16, #H17⟩
    wp_apply (wp_save W e γ m w v1 _ os1 c d1 qc (hardState.mk t vo (l + W64 1 + k)) esl es hf Hok1.1
      Hok1.2 h4 hfl.1 hsv.1 hsv.2) $$ [H5 H6 H7 H8 H9 H10 H11 H12 H14] as %b2 Hpost2
    · iframe
      iframe Hes H13 H15 H16 H17 H1 H2 H3 H4
    cases b2
    · try wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial
    try wp_auto
    ihave Hres2 := memSaveRes_post W e γ m w _ c qc _ es $$ [$Hpers Hpost2]
    · unfold memSavePost; iexact Hpost2
    icases Hres2 with ⟨%v2, %os2, %d2, Hres2, %Hok2⟩
    iunfold memSaveRes at Hres2
    icases Hres2 with ⟨-, -, -, -, H5, H6, H7, H8, H9, H10, H11, H12, -, H14, -, -, #H17⟩
    have hlen2 := tEncodeOracle_saveO_le (tSnapO o (l + W64 1 + k) t) (hardState.mk t vo (l + W64 1 + k)) es
    have hlen1 := tEncodeOracle_snapO o (l + W64 1 + k) t
    have hsm2 : tOrSmall (tSynced (tSaveO (tSnapO o (l + W64 1 + k) t)
        (hardState.mk t vo (l + W64 1 + k)) es)) := by
      unfold tOrSmall; rw [tEncodeOracle_synced]; unfold tOrRoom at hroom; omega
    wp_apply (wp_sync W e γ m w v2 _ os2 c d2 qc hf Hok2.1 hsm2)
      $$ [H5 H6 H7 H8 H9 H10 H11 H12 H14] as %b3 Hpost3
    · iframe
      iframe H1 H2 H3 H4 H13 H15 H17
    try wp_auto
    iapply HΦ
    icases Hpost3 with ⟨H5, H6, H7, H8, %v3, H9, H12, Hb3⟩
    cases b3
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial
    simp only [↓reduceIte]
    icases Hb3 with ⟨H10, H11, H14, #H17, #H16⟩
    have hsm2' : tOrSmall (tSaveO (tSnapO o (l + W64 1 + k) t) (hardState.mk t vo (l + W64 1 + k)) es) := by
      unfold tOrSmall; unfold tOrRoom at hroom; omega
    have hl2 := tOrSmall_since_lt hsm2'
    have hcw := tCheckWf_saveO (tCheckWf_snapO hwf hs63 hfl.1 hsnap) _ es h4 hfl.1 hsm2'
    iexists _
    isplitl
    · iunfold memLive
      iexists w, v3, _, c, d2, t, vo, (l + W64 1 + k), (l + W64 1 + k), l', mp, M', r, rvx
      iframe
      isplitl
      · iunfold memSaveRes
        iframe
        iframe H1 H2 H3 H4 H13 H15 H17
        rw [tSynced_mark _ c (by omega), ← tMemOk_len Hok2.1]
        iexact H16
      ipureintro
      exact ⟨tMemOk_synced Hok2.1 (by omega), Hok2.2, ⟨hfl.1, tTermsFrom_ok h5 ⟨hfl.1, tTermsOk_empty⟩⟩,
        tCheckWf_synced hcw (by omega)⟩
    · ipureintro
      rw [tEncodeOracle_synced]
      omega

end proof

end etcd_wal
end EtcdGrove
end Perennial
