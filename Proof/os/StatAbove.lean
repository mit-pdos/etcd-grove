/-
The proof of `Spec/os/StatAbove.lean` (`os.Stat.specAboveRoot`): `modelStat` at a strict
ancestor of a root answers with no extension step but the query `PathKind`
(`os.model.wp_stat_aboveS`, `Proof/os/StatAboveS.lean`).
-/
module

public import Proof.os.StatAboveS

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
variable [os.Assumptions]
  [go.BasicIntoValInj]

theorem os.Stat.wp_proofAboveRoot : os.Stat.specAboveRoot (GF := GF) (hG := hG) := by
  intro p R hp
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_aboveS p R (os.aboveRoot_rootsAbove hp) $$ Hpre as %fi %err -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
