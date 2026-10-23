/-
The trust boundary of `grpclog.SetLoggerV2` (see its spec).
-/
module

public import Spec.google_golang_org.grpc.grpclog.SetLoggerV2

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

/-- The trust boundary (see the spec's file header). -/
axiom grpclog.SetLoggerV2.wp_proof : grpclog.SetLoggerV2.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
