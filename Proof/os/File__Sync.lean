/-
The proof of `Spec/os/File__Sync.lean`: the model's `EINTR` loop runs once over `wp_osFsync`, which never
fails with `EINTR`.
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
  wp_apply wp_osFsync fd dq d m lo xs CoPset.subseteq_top $$ Hinv Hosfd Hm Hbs as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -, -⟩ | ⟨%he, -, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
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
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
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
