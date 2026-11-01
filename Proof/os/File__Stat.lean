/-
The proof of `Spec/os/File__Stat.lean`: the model's `EINTR` loop over `wp_osFstat`, and the `fileStat` it allocates, which
needs `fileStat.FieldAssumptions` (`TrustedCode/os.lean`).
-/
module

public import Spec.os.File__Stat

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

theorem os.File.Stat.wp_proof : os.File.Stat.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq dqm d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq, os.fileStat_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  iloeb as IH generalizing Hosfd Hm Hfd HΦ
  wp_apply wp_osFstat fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %sz %e %hr Hosfd Hm
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    try rw [os.fileStat_ty_eq]
    iapply IH $$ Hosfd Hm Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    rcases hr with ⟨rfl, rfl⟩ | ⟨he0, rfl⟩
    · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
      simp only [Bool.not_true]
      iapply wp_fupd
      wp_auto
      iStructNamed fs
      wp_auto
      ipersist size
      imodintro
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      ileft
      iexists fs_ptr
      unfold os.ownFileStat
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iassumption
    · have he0' : ¬ e = W64 0 := he0
      rw [decide_eq_false he0']
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      iright
      ipureintro; exact ⟨(fun h => by cases h), rfl⟩

end proof

end EtcdGrove
end Perennial
