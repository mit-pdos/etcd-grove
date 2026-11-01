/-
The proof of `Spec/os/File__Truncate.lean`: the model's `EINTR` loop, by Löb induction, over `wp_FtruncateStart` and `wp_FtruncateFinish`.
-/
module

public import Spec.os.File__Truncate

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

theorem os.File.Truncate.wp_proof : os.File.Truncate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
