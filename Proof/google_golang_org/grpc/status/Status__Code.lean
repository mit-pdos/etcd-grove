/-
Trust boundary: `(*status.Status).Code()` of a read-only status returns its code (an axiom; E1 (b),
approved by etcd-grove-81 2026-11-15; see `Spec/google_golang_org/grpc/status/Status__Code.lean`,
Go evidence `examples/premisefix/grpcstatusro`).
-/
module

public import Spec.google_golang_org.grpc.status.Status__Code

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `s.Code()` of a read-only status of code `c` returns `c`. -/
axiom status.Status.Code.wp_proof : status.Status.Code.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
