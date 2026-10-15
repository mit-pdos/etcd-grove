/- Lean-first (no Rocq counterpart).

`bitsetIndex(pos)`: two pure operations.
-/
module

public import Spec.github_com.anishathalye.porcupine.bitsetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem bitsetIndex.wp_proof : bitsetIndex.spec (GF := GF) (hG := hG) := fun pos => by
  wp_start
  wp_auto
  wp_end

end proof

end porcupine
end EtcdGrove
end Perennial
