/-
Trust boundary: `grpc.MaxConcurrentStreams` (an axiom; see `Spec/google_golang_org/grpc/MaxConcurrentStreams.lean`).
-/
module

public import Spec.google_golang_org.grpc.MaxConcurrentStreams

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

/-- **Trust boundary** (item 4, the server start): a connection's calls beyond `n` wait for a free
stream (HTTP/2's `SETTINGS_MAX_CONCURRENT_STREAMS`); a call that runs runs as without the option. -/
axiom grpc.MaxConcurrentStreams.wp_proof : grpc.MaxConcurrentStreams.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
