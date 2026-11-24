/-
The proof of `Spec/os/WriteFile.lean`, over `OpenFile.specCreateTruncS`, the empty `Write`
(`os.File.Write.wp_empty`) and `Close`. With `os.osAU_triv`, the update of a caller holding all of
its precondition. Lean-first.
-/
module

public import Spec.os.WriteFile
public import Spec.os.File__Close
public import Proof.os.OffLong
public import Proof.os.WriteFileLemmas

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
    as %f %err ⟨Hp, Hperm, %o, HQ, Hout, Htr, Hr⟩
  · iframe; (repeat' isplitl []) <;> iassumption
  ihave Hout := os.crOut_join j b h o $$ [HQ Hout]
  · iframe
  ihave Htr := os.crTr_false _ o $$ Htr
  icases Hr with (⟨%fd, %i, ⟨%herr, %hfd, %hio⟩, Hf, Ho, Hfd⟩ | ⟨%herr, #Hfe, -⟩)
  · subst herr
    wp_auto
    wp_apply os.File.Write.wp_empty f fd (child d b) (DFrac.own 1) sl dqs (W64 0) hfd
      $$ [Hf Ho Hsl] as %n %e ⟨-, Hf, Ho, Hsl, #He⟩
    · iframe
    have hsome : o.isSome = true := by
      rcases o with _ | ⟨x, s, i'⟩
      · simp only [crIno] at hio; rw [hnone] at hio; cases hio
      · rfl
    wp_apply wp_Close f fd (child d b) _ $$ [Hf Hfd] as %e1 ⟨-, -, #He1⟩
    · iframe; isplitr; iassumption; iapply lockToks_unlocked <;> rfl
    cases e1 <;> cases e <;> wp_auto <;>
      (iapply HΦ; isplitr; (· first | iexact He | iexact He1 | iapply fmtErrorOkOrNil_nil);
        iframe; ipureintro; intro _; exact hsome)
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok i =>
      wp_auto
      iapply HΦ
      isplitr
      · iexact Hfe
      iframe
      ipureintro; intro hc; cases hc

end proof

end EtcdGrove
end Perennial
