/-
The trust boundary: `Spec/container/heap/Init_.lean`. Lean-first.
-/
module

public import Spec.container.heap.Init_

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom heap.Init_.wp_proof : heap.Init_.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
