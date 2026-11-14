/-
The proof of `LinuxFs/Spec/os/WriteFileTrunc.lean`, over `os.OpenFile.wp_truncS` (the truncating open of
an existing file), the empty `Write` (`os.File.Write.wp_empty`) and `Close`, as
`os.WriteFile.wp_proofEmptyS`. Lean-first.
-/
module

public import LinuxFs.Spec.os.WriteFileTrunc
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.os.OffLong
public import LinuxFs.Proof.os.OpenFileTruncS

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

/-- A file held whole after a truncation is held whole (`trFile i P` forgets `P`'s facts). -/
theorem trFile_false (i : Ino) (P : Prop) : trFile (GF := GF) i P ⊢ trFile i False :=
  trFile_mono i P False False.elim

theorem os.WriteFile.wp_proofTruncS (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    os.WriteFile.specTruncS (GF := GF) (hG := hG) := by
  intro d b sl dqs perm R j i N dq dqn h qc hb hN hi
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, Hn, Htr, Hsl⟩
  wp_auto
  wp_apply os.OpenFile.wp_truncS d b (W64 1 ||| W64 64 ||| W64 512) perm R j i N dq dqn h qc
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hb hN hi
      $$ [Hp Hn Hperm Htr] as %f %err ⟨Hp, Hn, Hperm, Htr, Hr⟩
  · iframe; isplitl [] <;> iassumption
  ihave Htr := trFile_false i _ $$ Htr
  icases Hr with (⟨%fd, ⟨%herr, %hfd⟩, Hf, Ho, Hfd⟩ | ⟨%herr, -⟩)
  · subst herr
    wp_auto
    wp_apply os.File.Write.wp_empty f fd (child d b) (DFrac.own 1) sl dqs (W64 0) hfd
      $$ [Hf Ho Hsl] as %n %e ⟨-, Hf, Ho, Hsl⟩
    · iframe
    wp_apply wp_Close f fd (child d b) _ $$ [Hf Hfd] as %e1 ⟨-, -⟩
    · iframe; iassumption
    cases e1 <;> cases e <;> wp_auto <;> (iapply HΦ; iframe)
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok e =>
      wp_auto
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
