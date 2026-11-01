/-
The proof of `Spec/os/File__Stat.lean`: the model's `EINTR` loop over `wp_Fstat`, and the `fileStat` it allocates.
-/
module

public import Spec.os.File__Stat

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
variable [os.Assumptions]

theorem os.File.Stat.wp_proof : os.File.Stat.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
