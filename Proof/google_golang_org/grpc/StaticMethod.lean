/-
Trust boundary: `grpc.StaticMethod()` returns a `StaticMethodCallOption` (an axiom; see
`Spec/google_golang_org/grpc/StaticMethod.lean`).
-/
module

public import Spec.google_golang_org.grpc.StaticMethod

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: `grpc.StaticMethod()` is `StaticMethodCallOption{}` (grpc's
`rpc_util.go`, names only here). -/
axiom grpc.StaticMethod.wp_proof : grpc.StaticMethod.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
