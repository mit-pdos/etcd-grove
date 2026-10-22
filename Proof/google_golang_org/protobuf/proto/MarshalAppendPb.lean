/-
The trust boundary: `proto.MarshalOptions.MarshalAppend` of any message type (names-only; the message types are
`PbType`s, `InvProto.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalAppendPb

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

axiom proto.MarshalAppendPb.wp_proof : proto.MarshalAppendPb.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
