/-
The trust boundary: `proto.Marshal` of any message type at the bytes (names-only; the message types
are `PbType`s, `InvProto.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalPb

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

axiom proto.MarshalPb.wp_proof : proto.MarshalPb.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
