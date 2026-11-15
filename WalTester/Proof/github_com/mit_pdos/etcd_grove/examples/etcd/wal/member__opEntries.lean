/- Lean-first (no Rocq counterpart). The proof of `member.opEntries`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opEntries
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__next
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__size
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__hs
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save

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
theorem member.opEntries.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_next : rnd.next.spec (GF := GF) (hG := hG)) (wp_size : member.size.spec (GF := GF) (hG := hG))
    (wp_hs : member.hs.spec (GF := GF) (hG := hG)) (wp_save : member.save.spec (GF := GF) (hG := hG)) :
    member.opEntries.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc t vo cm bs l tm M r rv hf hok hhs ht hroom
  wp_start as ⟨Hres, Ht, Hv, Hc, Hb, Hl, Htm, HM, Hr, Hrv⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
    ileft
    iframe
    ipureintro; exact ⟨rfl, by word⟩
  wp_if_destruct
  all_goals
    wp_if_destruct
    wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv1, Hrv⟩, %hk⟩
    try wp_auto
    wp_if_destruct
    wp_apply wp_choose $$ [$Hrv] as %k2 ⟨⟨%rv2, Hrv⟩, %hk2⟩
    all_goals try wp_auto
  all_goals
    ihave Hlo : (∃ LO : w64, ⌜1 ≤ uint.nat LO ∧ uint.nat LO ≤ uint.nat l + 1⌝ ∗ lo_ptr ↦ LO) $$ [lo]
    · iexists _; iframe; ipureintro
      first | (rw [if_neg (by word)] at hk2; constructor <;> word) | (constructor <;> word)
    icases Hlo with ⟨%LO, %hLO, lo⟩
    wp_apply wp_choose $$ [$Hrv] as %kn ⟨⟨%rv3, Hrv⟩, %hkn⟩
    rw [if_neg (by decide)] at hkn
    wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %esl0 ⟨Hesl0, Hcap0⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    wp_auto
    have hn : uint.nat (W64 1 + kn) ≤ 4 ∧ 1 ≤ uint.nat (W64 1 + kn) := by constructor <;> word
    ihave HI : (∃ (i : w64) (esl : GoSlice) (es : List TEnt) (M' : GMap w64 w64) (rvx : rnd),
        "i" ∷ i_ptr ↦ i ∗ "es" ∷ es_ptr ↦ esl ∗ "Hes" ∷ esl ↦* es ∗
        "Hcap" ∷ ownSliceCap TEnt esl (DFrac.own 1) ∗ "HM" ∷ tm ↦$ M' ∗ "Hrv" ∷ r ↦ rvx ∗
        "%Hi" ∷ ⌜uint.nat LO ≤ uint.nat i ∧ uint.nat i ≤ uint.nat LO + uint.nat (W64 1 + kn) ∧
          es.length = uint.nat i - uint.nat LO ∧ (∀ x ∈ es, tEntWf x ∧ x.term' = t) ∧
          tTermsFrom t M M'⌝ : IProp GF) $$ [i es Hesl0 Hcap0 HM Hrv]
    · iexists LO, esl0, [], M, rv3
      iframe
      ipureintro
      refine ⟨Nat.le_refl _, by omega, by simp, by simp, tTermsFrom_refl t M⟩
    wp_for HI
    by_cases hlt : uint.nat i < uint.nat LO + uint.nat (W64 1 + kn)
    · have hlt' : uint.Z i < uint.Z (LO + (W64 1 + kn)) := by word
      simp only [hlt', _root_.decide_true, ↓reduceIte]
      wp_auto
      wp_apply (wp_size m r rvx) $$ [$Hr $Hrv] as %sz ⟨Hr, ⟨%rvy, Hrv⟩, %hsz⟩
      wp_apply (wp_next r rvy) $$ [$Hrv] as %x ⟨%rvz, Hrv⟩
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append $$ [$Hes $Hcap $Hosl] as %esl2 ⟨Hes2, Hcap2, -⟩
      wp_apply (wp_mapInsert go.uint64 tm M' i t) $$ [$HM] as HM
      wp_for_post
      iframe
      iexists i + W64 1, esl2, es ++ [entry.mk i t sz x], <[i := t]> M', rvz
      iframe
      ipureintro
      obtain ⟨h1, h2, h3, h4, h5⟩ := Hi
      have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      refine ⟨by omega, by omega, by simp only [List.length_append, List.length_singleton]; omega, ?_, tTermsFrom_insert h5 i⟩
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact h4 y hy
      · simp only [List.mem_singleton] at hy
        subst hy
        refine ⟨⟨by simp; omega, by simp; omega, by simp; word, by simpa using ht⟩, rfl⟩
    · have hlt' : ¬ uint.Z i < uint.Z (LO + (W64 1 + kn)) := by word
      simp only [hlt', decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte, val_false_ne_true,
        not_false_eq_true]
      obtain ⟨h1, h2, h3, h4, h5⟩ := Hi
      have hin : uint.nat i = uint.nat LO + uint.nat (W64 1 + kn) := by omega
      wp_auto
      ihave HI2 : (∃ (j : w64) (M'' : GMap w64 w64), "i" ∷ i_ptr ↦ j ∗ "HM" ∷ tm ↦$ M'' ∗
          "%Hj" ∷ ⌜tTermsFrom t M M''⌝ : IProp GF) $$ [i HM]
      · iexists _, M'; iframe; ipureintro; exact h5
      wp_for HI2
      by_cases hle : uint.Z j ≤ uint.Z l
      · simp only [hle, _root_.decide_true, ↓reduceIte]
        wp_auto
        wp_apply (wp_mapDelete tm M'' j go.uint64 go.uint64) $$ [$HM] as HM
        wp_for_post
        iframe
        iexists j + W64 1, GMap.delete j M''
        iframe
        ipureintro; exact tTermsFrom_delete Hj j
      · simp only [hle, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte, val_false_ne_true,
          not_false_eq_true]
        wp_auto
        have hesl : es.length ≤ 4 ∧ 1 ≤ es.length := by omega
        wp_apply wp_choose $$ [$Hrv] as %k3 ⟨⟨%rv4, Hrv⟩, -⟩
        wp_if_destruct
        wp_if_destruct
        wp_apply wp_choose $$ [$Hrv] as %k4 ⟨⟨%rv5, Hrv⟩, -⟩
        all_goals try wp_auto
        all_goals
          ihave Hc : (∃ cm' : w64, m.[member, go!"commit"] ↦ cm') $$ [Hc]
          · iexists _; iexact Hc
          icases Hc with ⟨%cm', Hc⟩
          ihave Hl : (∃ l' : w64, m.[member, go!"last"] ↦ l') $$ [Hl]
          · iexists _; iexact Hl
          icases Hl with ⟨%l', Hl⟩
          wp_apply (wp_hs m t vo cm') $$ [$Ht $Hv $Hc] as ⟨Ht, Hv, Hc⟩
          imod ownSlice_persist $$ Hes with #Hes
          try wp_auto
          iunfold memSaveRes at Hres
          icases Hres with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, H10, H11, H12, #H13, H14, #H15, #H16, #H17⟩
          wp_apply (wp_save W e γ m w v o os c d qc (hardState.mk t vo cm') esl es hf hok hhs
            (fun x hx => (h4 x hx).1) ht (tOrRoom_save hroom (by omega) _).1 (tOrRoom_save hroom (by omega) _).2)
            $$ [H5 H6 H7 H8 H9 H10 H11 H12 H14] as %b Hpost
          · iframe
            iframe Hes H13 H15 H16 H17 H1 H2 H3 H4
          iapply HΦ
          iframe
          iright
          iexists cm', l', es, M''
          unfold memSavePost
          iframe
          ipureintro
          exact ⟨hesl.2, hesl.1, h4, Hj⟩

end proof

end etcd_wal
end EtcdGrove
end Perennial
