/-
Trust boundary: `(*GenericClientStream[Req, Res]).Context()`, promoted from the embedded `ClientStream` (an axiom; see
`Spec/google_golang_org/grpc/GenericClientStream__Context.lean`: Goose does not translate methods of generic types).
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__Context

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

/-- **Trust boundary** (W-W): `(*GenericClientStream[Req, Res]).Context()`, promoted from the embedded `ClientStream`: `x.ClientStream.Context()`. -/
axiom grpc.GenericClientStream.Context.wp_proof : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
