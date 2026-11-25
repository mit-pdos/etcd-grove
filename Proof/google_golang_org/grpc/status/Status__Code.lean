/-
`(*status.Status).Code()` of a read-only status returns its code: proved over grpc's translated
`internal/status` (status-bodies, 2026-11-25; until then a trust-boundary axiom, E1 (b), approved by
etcd-grove-81 2026-11-15, Go evidence `examples/premisefix/grpcstatusro`).
-/
module

public import Spec.google_golang_org.grpc.status.Status__Code
public import Proof.google_golang_org.grpc.internal.status.Methods

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
variable [package_sem : google_golang_org.grpc.internal.status.Assumptions]

/-- `s.Code()` of a read-only status of code `c` returns `c` (`wp_Status_Code_ro`). -/
theorem status.Status.Code.wp_proof : status.Status.Code.spec (GF := GF) (hG := hG) :=
  fun s c m => wp_Status_Code_ro s c m

end proof

end EtcdGrove
end Perennial
