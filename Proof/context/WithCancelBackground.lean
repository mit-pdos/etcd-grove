/-
Proof of `Spec/context/WithCancelBackground.lean`: a trust-boundary axiom (rafthttp stage 4d). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.context.WithCancelBackground

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **Trust boundary** (rafthttp stage 4d): Go's `WithCancel(Background())`: a `*cancelCtx` whose parent is never
done (`propagateCancel` returns at once), cancelled only by its `cancel`. -/
axiom context.WithCancelBackground.wp_proof : context.WithCancelBackground.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
