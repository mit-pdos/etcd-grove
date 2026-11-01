/-
The proofs of `Spec/os/Crash.lean`: the models' loops as in `Proof/os/OpenFile.lean`,
`Proof/os/File__WriteAt.lean` and `Proof/syscall/Fdatasync.lean`, over the crash-aware steps of
`Proof/os/CrashOps.lean`. A write's loop keeps a narrowing of the file it started from
(`narrow_fin`), whose crashes the first attempt's cover (`crashOk_narrow`).
-/
module

public import Spec.os.Crash

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

theorem syscall.Fdatasync.wp_proof_crash [syscall.Assumptions] :
    syscall.Fdatasync.specCrash (GF := GF) (hG := hG) := by
  intro fd dq d N γ Good m bs hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cf fd dq d N γ Good m bs hN hok $$ Hos Hinv Hfd Hown as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

variable [os.Assumptions]

theorem os.OpenFile.wp_proof_crash [os.file.FieldAssumptions] :
    os.OpenFile.specCrash (GF := GF) (hG := hG) := by
  intro path perm N γ Good s hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  ihave Hown := (show cfOwn path γ s ⊢ cfOwn path γ s' by rw [hs']) $$ Hown
  have hm2 : s' = s ∨ s' = openState s := .inl hs'
  clear hs'
  iloeb as IH generalizing %s' %hm2 Hown HΦ
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  have hs2 : s' = none ∨ ∃ m bs, s' = some (m, bs, none) := by
    rcases hm2 with rfl | rfl
    · exact hs
    · rcases hs with rfl | ⟨m, bs, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
      · exact .inr ⟨_, _, rfl⟩
  have hos : openState s' = openState s := by
    rcases hm2 with rfl | rfl
    · rfl
    · rcases hs with rfl | ⟨m, bs, rfl⟩ <;> rfl
  wp_apply wp_osOpen_cf path (W64 0x80042) N γ Good s' hs2 hN
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide)
    (by rw [hos]; exact hok) $$ Hos Hinv Hown as %fd %e %s2 %hres Hown Hfd
  have hfd : openFd path (W64 0x80042) = ⟨path, true, true⟩ := by
    simp [openFd, O_WRONLY, O_RDONLY]
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd path (W64 524354)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨path, true, true⟩
      by rw [hfd]; split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    obtain ⟨-, hfd0, hs2e⟩ := hres.resolve_right (fun h => h.1 rfl)
    rw [hos] at hs2e
    subst hs2e
    iapply HΦ
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0]
    iclear Hfd
    have hm3 : s2 = s ∨ s2 = openState s := by
      rcases hres with ⟨h, -⟩ | ⟨-, -, h | h⟩
      · exact absurd h he0
      · rw [h]; exact hm2
      · rw [h, hos]; exact .inr rfl
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      try rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
      iapply IH $$ %_ %hm3 Hown HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists s2
      iframe
      ipureintro; exact hm3

end proof

end EtcdGrove
end Perennial
