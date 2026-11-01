/-
The proof of `Spec/os/OpenFile.lean`: the model's `EINTR` loop, by Löb induction, over `wp_Open`;
the `file` it allocates needs `file.FieldAssumptions` (`TrustedCode/os.lean`).
-/
module

public import Spec.os.OpenFile

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
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem os.OpenFile.wp_proof : os.OpenFile.spec (GF := GF) (hG := hG) := by
  intro path perm q mo hq
  wp_start as ⟨#Hinv, Hm⟩
  obtain ⟨mo', hmo'⟩ : ∃ mo', mo' = mo := ⟨_, rfl⟩
  ihave Hm := (show osMeta path q mo ⊢ osMeta path q mo' by rw [hmo']) $$ Hm
  have hm2 : mo' = mo ∨ mo' = openMeta mo true := .inl hmo'
  clear hmo'
  iloeb as IH generalizing %mo' %hm2 Hm HΦ
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  have hq' : mo' = none → q = DFrac.own 1 := by
    intro h; rcases hm2 with rfl | rfl
    · exact hq h
    · cases mo <;> simp [openMeta] at h
  wp_apply wp_Open path (W64 0x80042) q mo' CoPset.subseteq_top
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hq'
    $$ Hinv Hm as %fd %e %mo2 %hres Hm Hfd
  have hom : openMeta mo' true = openMeta mo true := by
    rcases hm2 with rfl | rfl
    · rfl
    · cases mo <;> rfl
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
    have hcr : decide ((W64 524354).toNat / O_CREAT % 2 = 1) = true := by decide
    obtain ⟨-, -, hmo2, -⟩ := hres.resolve_right (fun h => h.1 rfl)
    rw [hcr, hom] at hmo2
    subst hmo2
    iapply HΦ
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; rfl
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0]
    iclear Hfd
    have hmo2 : mo2 = mo ∨ mo2 = openMeta mo true := by
      have hcr : decide ((W64 524354).toNat / O_CREAT % 2 = 1) = true := by decide
      rcases hres with ⟨h, -⟩ | ⟨-, -, h | h⟩
      · exact absurd h he0
      · rw [h]; exact hm2
      · rw [h, hcr, hom]; exact .inr rfl
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      try rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
      iapply IH $$ %_ %hmo2 Hm HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists mo2
      iframe
      ipureintro; exact hmo2

end proof

end EtcdGrove
end Perennial
