/-
Proof of `Spec/context/WithCancelTodo.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.context.WithCancelTodo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **Trust boundary** (item 5): Go's `WithCancel(TODO())`: a `*cancelCtx` whose parent is never
done (`propagateCancel` returns at once), cancelled only by its `cancel`. -/
axiom context.WithCancelTodo.wp_proof : context.WithCancelTodo.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
