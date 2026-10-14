/-
The trust boundary: `heap.Fix` (`container/heap`, a standard-library package Perennial does not
translate; names only here). See `Proof/container/heap/Defs.lean`.
-/
module

public import Spec.container.heap.Fix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom heap.Fix.wp_proof : heap.Fix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
