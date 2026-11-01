/-
The proof of `Spec/os/File__Truncate.lean`: the model's `EINTR` loop, by Löb induction, over `wp_osFtruncateStart` and `wp_osFtruncateFinish`.
-/
module

public import Spec.os.File__Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.Truncate.wp_proof : os.File.Truncate.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d m hi hfd0 hwr hsz hgrow hhi
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have h1 : ¬ (sint.Z fd < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd0
  rw [decide_eq_false h1]
  wp_auto
  have h2 : ¬ (sint.Z sz < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hsz
  rw [decide_eq_false h2]
  wp_auto
  have hpost : ∀ (m0 : OsMeta) (e : w64), (m0 = m ∨ m0 = ftMeta m sz.toNat) →
      (((⌜e = 0⌝ ∗ osGrown (GF := GF) d.path m0 sz.toNat hi) ∨
        (⌜e ≠ 0⌝ ∗ (osGrown d.path m0 sz.toNat hi ∨
          (osMeta d.path (DFrac.own 1) (some (ftMeta m0 sz.toNat)) ∗
            mcellsAny m0.maps m0.size hi)))) ⊢
      ((⌜e = 0⌝ ∗ osGrown d.path m sz.toNat hi) ∨
        (⌜e ≠ 0⌝ ∗ (osGrown d.path m sz.toNat hi ∨
          (osMeta d.path (DFrac.own 1) (some (ftMeta m sz.toNat)) ∗
            mcellsAny m.maps m.size hi))))) := by
    rintro m0 e (rfl | rfl)
    · exact .rfl
    · have h1 : ftMeta (ftMeta m sz.toNat) sz.toNat = ftMeta m sz.toNat := by
        cases m; simp only [ftMeta, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega
      have h2 : osGrown (GF := GF) d.path (ftMeta m sz.toNat) sz.toNat hi =
          osGrown d.path m sz.toNat hi := by
        have : (ftMeta m sz.toNat).grown sz.toNat = m.grown sz.toNat := by
          cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega
        unfold osGrown; rw [this]; rfl
      rw [h1, h2]; exact .rfl
  ihave HS : (∃ m0, ⌜m0 = m ∨ m0 = ftMeta m sz.toNat⌝ ∗
      osMeta d.path (DFrac.own 1) (some m0) ∗ mcellsAny m.maps m.size hi) ∨
      osGrown d.path m sz.toNat hi $$ [Hm Hc]
  · ileft; iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with (⟨%m0, %hm0, Hm, Hc⟩ | Hg)
  · ihave Hc := (show mcellsAny (GF := GF) m.maps m.size hi ⊢ mcellsAny m0.maps m0.size hi by
      rcases hm0 with rfl | rfl <;> exact .rfl) $$ Hc
    have hgrow0 : m0.size ≤ sz.toNat := by rcases hm0 with rfl | rfl <;> exact hgrow
    have hhi0 : MapsBelow m0.maps hi := by rcases hm0 with rfl | rfl <;> exact hhi
    wp_apply wp_osFtruncateStart fd sz dq d m0 hi CoPset.subseteq_top hwr hsz hgrow0 hhi0
      $$ Hinv Hosfd Hm Hc as %t Hosfd Ht
    wp_apply wp_osFtruncateFinish t d.path sz.toNat m0 hi CoPset.subseteq_top hgrow0 hhi0
      $$ Hinv Ht as %e Hr0
    ihave Hr := hpost m0 e hm0 $$ Hr0
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] Hosfd Hfd HΦ
      icases HS with (H | ⟨Hm, Hc⟩)
      · iright; iexact H
      · ileft; iexists (ftMeta m sz.toNat); iframe; ipureintro; exact .inr rfl
    · rw [decide_eq_false he4]
      wp_auto
      icases Hr with (⟨%he, Hg⟩ | ⟨%he, HS⟩)
      · subst he
        rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        ileft
        iframe
        ipureintro; rfl
      · have he0' : ¬ e = W64 0 := he
        rw [decide_eq_false he0']
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        iright
        iframe
        ipureintro; intro h; cases h
  · unfold osGrown
    icases Hg with ⟨Hm, Hbs, Hcs, Hc⟩
    have hgg : (m.grown sz.toNat).grown sz.toNat = m.grown sz.toNat := by
      simp [OsMeta.grown]
    have hgf : ftMeta (m.grown sz.toNat) sz.toNat = m.grown sz.toNat := by
      cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega
    ihave Hc := (show mcellsAny (GF := GF) m.maps sz.toNat hi ⊢
      mcellsAny (m.grown sz.toNat).maps (m.grown sz.toNat).size hi by simp only [OsMeta.grown]; iintro H; iexact H) $$ Hc
    wp_apply wp_osFtruncateStart fd sz dq d (m.grown sz.toNat) hi CoPset.subseteq_top hwr hsz
      (Nat.le_refl _) hhi $$ Hinv Hosfd Hm Hc as %t Hosfd Ht
    wp_apply wp_osFtruncateFinish t d.path sz.toNat (m.grown sz.toNat) hi CoPset.subseteq_top
      (Nat.le_refl _) hhi $$ Hinv Ht as %e Hr0
    ihave Hr : (⌜e = 0⌝ ∗ osGrown d.path m sz.toNat hi) ∨
        (⌜e ≠ 0⌝ ∗ (osGrown d.path m sz.toNat hi ∨
          (osMeta d.path (DFrac.own 1) (some (ftMeta m sz.toNat)) ∗
            mcellsAny m.maps m.size hi))) $$ [Hr0 Hbs Hcs]
    · unfold osGrown
      icases Hr0 with (⟨%he, ⟨Hm, -, -, Hc⟩⟩ | ⟨%he, (⟨Hm, -, -, Hc⟩ | ⟨Hm, Hc⟩)⟩)
      · ileft; rw [hgg]; iframe; ipureintro; exact he
      · iright; isplitr; · ipureintro; exact he
        ileft; rw [hgg]; iframe
      · iright; isplitr; · ipureintro; exact he
        ileft; rw [hgf]; iframe
    unfold osGrown
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] Hosfd Hfd HΦ
      icases HS with (H | ⟨Hm, Hc⟩)
      · iright; iexact H
      · ileft; iexists (ftMeta m sz.toNat); iframe; ipureintro; exact .inr rfl
    · rw [decide_eq_false he4]
      wp_auto
      icases Hr with (⟨%he, Hg⟩ | ⟨%he, HS⟩)
      · subst he
        rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        ileft
        iframe
        ipureintro; rfl
      · have he0' : ¬ e = W64 0 := he
        rw [decide_eq_false he0']
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        iright
        iframe
        ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
