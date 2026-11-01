/-
The proof of `Spec/golang_org/x/sys/unix/Munmap.lean`: `wp_Munmap`.
-/
module

public import Spec.golang_org.x.sys.unix.Munmap

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
variable [golang_org.x.sys.unix.Assumptions]

theorem golang_org.x.sys.unix.Munmap.wp_proof : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
