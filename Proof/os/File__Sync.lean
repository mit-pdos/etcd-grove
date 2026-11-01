/-
The proof of `Spec/os/File__Sync.lean`: the model's `EINTR` loop, by Löb induction, over `wp_Fsync`.
-/
module

public import Spec.os.File__Sync

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

theorem os.File.Sync.wp_proof : os.File.Sync.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m lo xs
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm, Hbs⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  ihave Hm := (show osMeta d.path (DFrac.own 1) (some m) ⊢ osMeta d.path (DFrac.own 1) (some m')
    by rw [hm']) $$ Hm
  have hm2 : m' = m ∨ m' = { m with ok := false } := .inl hm'
  clear hm'
  iloeb as IH generalizing %m' %hm2 Hosfd Hm Hbs Hfd HΦ
  wp_apply wp_Fsync fd dq d m' lo xs CoPset.subseteq_top $$ Hinv Hosfd Hm Hbs as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    icases Hr with (⟨%he, -, -⟩ | ⟨-, Hm, Hbs⟩)
    · exact absurd (he4 ▸ he) (by decide)
    have hm3 : { m' with ok := false } = { m with ok := false } := by
      rcases hm2 with rfl | rfl <;> rfl
    rw [hm3]
    iapply IH $$ %_ %(.inr rfl) Hosfd Hm Hbs Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    icases Hr with (⟨%he, Hm, Hbs⟩ | ⟨%he, Hm, Hbs⟩)
    · subst he
      rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      ileft
      isplitr; · ipureintro; rfl
      rcases hm2 with rfl | rfl
      · ileft; iframe
      · iright
        have : syncedBytes { m with ok := false } xs = xs := by simp [syncedBytes]
        rw [this]; iframe
    · have he0' : ¬ e = W64 0 := he
      simp only [decide_eq_false he0', Bool.not_false]
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
      have hm3 : { m' with ok := false } = { m with ok := false } := by
        rcases hm2 with rfl | rfl <;> rfl
      rw [hm3]
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
