/-
The proof of `Spec/os/fileStat__Name.lean`: one load.
-/
module

public import LinuxFs.Spec.os.fileStat__Name

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.fileStat.Name.wp_proof : os.fileStat.Name.spec (GF := GF) (hG := hG) := by
  intro fs sz
  unfold os.ownFileStat
  wp_start as ⟨#Hs, ⟨%mode, #Hm⟩, %nm, #Hnm⟩
  wp_auto
  iapply HΦ
  isplitl []
  · iassumption
  isplitl []
  · iexists mode; iassumption
  iexists nm
  iassumption

end proof

end EtcdGrove
end Perennial
