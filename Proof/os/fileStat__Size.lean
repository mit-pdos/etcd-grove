/-
The proof of `Spec/os/fileStat__Size.lean`: one load.
-/
module

public import Spec.os.fileStat__Size

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.fileStat.Size.wp_proof : os.fileStat.Size.spec (GF := GF) (hG := hG) := by
  intro fs sz
  unfold os.ownFileStat
  wp_start as #Hs
  wp_auto
  iapply HΦ
  iassumption

end proof

end EtcdGrove
end Perennial
