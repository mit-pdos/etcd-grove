/-
**Trust boundary**: `(*ClientConn).Close()` closes the connection for good (an axiom; see
`Spec/google_golang_org/grpc/ClientConn__Close.lean`; grpc-trusted-T, T8, interim, retired by phase 7's
S2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Close

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

/-- **Trust boundary** (T8): `(*ClientConn).Close()` returns, the connection closed for good
(`models/grpc/clientconn.go:633-658`). -/
axiom grpc.ClientConn.Close.wp_proof : grpc.ClientConn.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
