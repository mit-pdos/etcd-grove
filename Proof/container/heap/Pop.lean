/-
The trust boundary: `Spec/container/heap/Pop.lean`. Lean-first.
-/
module

public import Spec.container.heap.Pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom heap.Pop.wp_proof : heap.Pop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
