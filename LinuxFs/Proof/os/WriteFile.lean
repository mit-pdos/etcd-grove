/-
The proof of `LinuxFs/Spec/os/WriteFile.lean`, over `OpenFile.specCreateTruncS`, the empty `Write`
(`os.File.Write.wp_empty`) and `Close`. With `os.osAU_triv`, the update of a caller holding all of
its precondition. Lean-first.
-/
module

public import LinuxFs.Spec.os.WriteFile
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.os.OffLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- **The trivial update** of a caller holding all of `α`: it commits with whatever the step gives. -/
theorem os.osAU_triv {A : Type} (α : IProp GF) (β : A → IProp GF) : α ⊢ osAU α β β := by
  unfold osAU
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, Hα⟩
  unfold atomic_acc
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iframe Hα
  isplit
  · iintro Hα
    imod Hclose
    imodintro
    iexact Hα
  · iintro %o Hβ
    imod Hclose
    imodintro
    iexact Hβ

/-- Two halves of a create's outcome on a claim make the whole. -/
theorem os.crOut_join (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ∗ crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ⊢
      crOut (GF := GF) j b h (DFrac.own 1) o := by
  rcases o with _ | ⟨x, s, i⟩
  · dsimp only [crOut]
    iintro ⟨H1, H2⟩
    iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1
    iframe
  · dsimp only [crOut]
    iintro ⟨⟨%hc, Hl, H1⟩, ⟨-, -, H2⟩⟩
    iframe Hl
    isplitr
    · ipureintro; exact hc
    iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1
    iframe

theorem os.WriteFile.wp_proofEmptyS (wp_Open : os.OpenFile.specCreateTruncS (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    os.WriteFile.specEmptyS (GF := GF) (hG := hG) := by
  intro d b sl dqs perm R j dq h qc hb hnone
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn, Hsl⟩
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hq, Hr⟩
  ihave Hau := os.osAU_triv (osNames j (.only [b]) (DFrac.own (1 : Qp).half) h)
    (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
  wp_auto
  wp_apply wp_Open d b (W64 1 ||| W64 64 ||| W64 512) perm R j dq h (1 : Qp).half (1 : Qp).half qc
      (crOut j b h (DFrac.own (1 : Qp).half))
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide)
      hb hnone (Qp.half_add_half 1) $$ [Hp Hperm Hq Hau]
    as %f %err ⟨Hp, Hperm, %o, HQ, Hout, -, Hr⟩
  · iframe; isplitl [] <;> iassumption
  ihave Hout := os.crOut_join j b h o $$ [HQ Hout]
  · iframe
  icases Hr with (⟨%fd, %i, ⟨%herr, %hfd, %hio⟩, Hf, Ho, Hfd⟩ | ⟨%herr, -⟩)
  · subst herr
    wp_auto
    wp_apply os.File.Write.wp_empty f fd (child d b) (DFrac.own 1) sl dqs (W64 0) hfd
      $$ [Hf Ho Hsl] as %n %e ⟨-, Hf, Ho, Hsl⟩
    · iframe
    have hsome : o.isSome = true := by
      rcases o with _ | ⟨x, s, i'⟩
      · simp only [crIno] at hio; rw [hnone] at hio; cases hio
      · rfl
    wp_apply wp_Close f fd (child d b) _ $$ [Hf Hfd] as %e1 ⟨-, -⟩
    · iframe; iassumption
    cases e1 <;> cases e <;> wp_auto <;>
      (iapply HΦ; iframe; ipureintro; intro _; exact hsome)
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok i =>
      wp_auto
      iapply HΦ
      iframe
      ipureintro; intro hc; cases hc

end proof

end EtcdGrove
end Perennial
