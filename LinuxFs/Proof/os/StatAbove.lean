/-
The proof of `LinuxFs/Spec/os/StatAbove.lean` (`os.Stat.specAboveRoot`): `model.stat` at a strict
ancestor of a root answers with no extension step but the query `PathKind`
(`os.model.wp_stat_aboveS`).
-/
module

public import LinuxFs.Proof.os.NsAbove

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
  [go.BasicIntoValInj]

theorem os.Stat.wp_proofAboveRoot : os.Stat.specAboveRoot (GF := GF) (hG := hG) := by
  intro p R qc hp
  wp_start as ⟨#Hos, #Hsi, Hperm⟩
  wp_apply os.model.wp_stat_aboveS _ p R (os.aboveRoot_rootsAbove hp) $$ [Hos Hsi]
    as %fi %err -
  · isplitl [] <;> iassumption
  iapply HΦ
  iexact Hperm

end proof

end EtcdGrove
end Perennial
