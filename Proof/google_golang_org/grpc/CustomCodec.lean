/-
Trust boundary: `grpc.CustomCodec` (an axiom; see `Spec/google_golang_org/grpc/CustomCodec.lean`).
-/
module

public import Spec.google_golang_org.grpc.CustomCodec

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

/-- **Trust boundary** (item 4, the server start): the server marshals and unmarshals messages with
`c`; a protobuf codec is what the default codec is, so what a run is given (`grpcDecOk`, the wire
models) is unchanged. -/
axiom grpc.CustomCodec.wp_proof : grpc.CustomCodec.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
