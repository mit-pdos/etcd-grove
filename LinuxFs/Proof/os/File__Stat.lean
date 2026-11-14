/-
The proof of `Spec/os/File__Stat.lean`: the model's `EINTR` loop over `wp_osFstat`, and the `fileStat` it allocates, which
needs `fileStat.FieldAssumptions` (`TrustedCode/os.lean`).
-/
module

public import LinuxFs.Proof.os.ErrorOk
public import LinuxFs.Proof.os.PathParent
public import LinuxFs.Spec.os.File__Stat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

theorem os.File.Stat.wp_proof : os.File.Stat.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq dqm d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm⟩
  unfold os.model.inner os.model.arbitraryMode
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
      try wp_auto
      wp_apply os.model.wp_base as %nm _
      try wp_auto
      wp_apply wp_ArbitraryInt as %x _
      ipersist name
      ipersist size
      ipersist mode
      imodintro
      ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
      iapply HΦ
      iframe Hokn
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      isplitr
      rotate_left
      · ileft; ipureintro; rfl
      ileft
      iexists fs_ptr
      unfold os.ownFileStat
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl []
      · iassumption
      isplitl []
      · iexists _; iassumption
      iexists _
      iassumption
    · have he0' : ¬ e = W64 0 := he0
      rw [decide_eq_false he0']
      wp_auto
      wp_apply os.wp_wrapErrno_errno _ inner name e $$ Hn as %perr #Hep
      ihave #Hok := os.errnoPathErr_fmtErrorOk perr e he0' $$ Hep
      ihave %Hne := os.errnoPathErr_ne perr e $$ Hep
      ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
      iapply HΦ
      iframe Hokn
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      isplitr
      rotate_left
      · iright; iexists e; iframe Hep; ipureintro; exact he0'
      iright
      ipureintro; exact ⟨Hne, rfl⟩

end proof

end EtcdGrove
end Perennial
