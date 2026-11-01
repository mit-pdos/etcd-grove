/-
The proof of `Spec/os/File__Truncate.lean`: the model's `EINTR` loop, by Löb induction, over `wp_FtruncateStart` and `wp_FtruncateFinish`.
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
  intro f fd name dqf sz dq d m hfd0 hwr hsz hgrow
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
  ihave HS : (osMeta d.path (DFrac.own 1) (some m) ∗ mcellsAny m.maps m.size sz.toNat) ∨
      osGrown d.path m sz.toNat $$ [Hm Hc]
  · ileft; iframe
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with (⟨Hm, Hc⟩ | Hg)
  · wp_apply wp_FtruncateStart fd sz dq d m CoPset.subseteq_top hwr hsz hgrow
      $$ Hinv Hosfd Hm as %t Hosfd Ht
    wp_apply wp_FtruncateFinish t d.path sz.toNat m CoPset.subseteq_top hgrow
      $$ Hinv Ht Hc as %e Hr
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] Hosfd Hfd HΦ
      icases HS with (H | H)
      · iright; iexact H
      · ileft; iexact H
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
    icases Hg with ⟨Hm, Hbs, Hcs⟩
    have hgg : (m.grown sz.toNat).grown sz.toNat = m.grown sz.toNat := by
      simp [OsMeta.grown]
    wp_apply wp_FtruncateStart fd sz dq d (m.grown sz.toNat) CoPset.subseteq_top hwr hsz
      (Nat.le_refl _) $$ Hinv Hosfd Hm as %t Hosfd Ht
    ihave Hc0 := mcellsAny_nil (GF := GF) (m.grown sz.toNat).maps (m.grown sz.toNat).size
      sz.toNat rfl
    wp_apply wp_FtruncateFinish t d.path sz.toNat (m.grown sz.toNat) CoPset.subseteq_top
      (Nat.le_refl _) $$ Hinv Ht Hc0 as %e Hr0
    ihave Hr : (⌜e = 0⌝ ∗ osGrown d.path m sz.toNat) ∨
        (⌜e ≠ 0⌝ ∗ (osGrown d.path m sz.toNat ∨
          (osMeta d.path (DFrac.own 1) (some m) ∗ mcellsAny m.maps m.size sz.toNat))) $$ [Hr0 Hbs Hcs]
    · unfold osGrown
      icases Hr0 with (⟨%he, ⟨Hm, -, -⟩⟩ | ⟨%he, (⟨Hm, -, -⟩ | ⟨Hm, -⟩)⟩)
      · ileft; rw [hgg]; iframe; ipureintro; exact he
      · iright; isplitr; · ipureintro; exact he
        ileft; rw [hgg]; iframe
      · iright; isplitr; · ipureintro; exact he
        ileft; iframe
    unfold osGrown
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
      · exact absurd (he4 ▸ he) (by decide)
      iapply IH $$ [HS] Hosfd Hfd HΦ
      icases HS with (H | H)
      · iright; iexact H
      · ileft; iexact H
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
