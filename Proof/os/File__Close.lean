/-
The proof of `Spec/os/File__Close.lean`: a store of -1 to the fd field, and `wp_Close`.
-/
module

public import Spec.os.File__Close

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

theorem os.File.Close.wp_proof : os.File.Close.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
