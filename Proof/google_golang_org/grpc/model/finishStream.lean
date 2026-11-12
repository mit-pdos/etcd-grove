/-
Proof of `Spec/google_golang_org/grpc/model/finishStream.lean`: a trust-boundary axiom (per-type stage B,
B1a, 2026-11-11), the whole semantics of the model-only name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.model.finishStream

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

/-- **Trust boundary**: see `grpc.model.finishStream.spec`'s docstring (the Go composite it stands for). -/
axiom grpc.model.finishStream.wp_proof : grpc.model.finishStream.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
