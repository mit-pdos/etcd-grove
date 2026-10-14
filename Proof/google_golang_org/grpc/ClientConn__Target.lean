/-
**Trust boundary**: `(*ClientConn).Target()` returns its target (an axiom; see `Spec/google_golang_org/grpc/ClientConn__Target.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Target

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

/-- **Trust boundary**: `(*ClientConn).Target()` returns its target. -/
axiom grpc.ClientConn.Target.wp_proof : grpc.ClientConn.Target.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
