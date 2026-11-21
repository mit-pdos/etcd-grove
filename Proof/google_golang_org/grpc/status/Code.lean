/-
**Trust boundary**: `status.Code` of an error grpc accepts returns (an axiom; see `Spec/google_golang_org/grpc/status/Code.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.status.Code

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `status.Code` of an error grpc accepts returns. It reads the `*Status` the
error's `GRPCStatus()` returns: justified by the premise, whose `grpcErrMethodsOk` gives that status
read-only (`status.statusAt`; E1, 2026-11-15; it was a latent assumption,
`notes/axiom-review/grpc-status-immutability.md`). -/
axiom status.Code.wp_proof : status.Code.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
