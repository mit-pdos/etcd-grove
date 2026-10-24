/-
The trust boundary: `proto.Size` of any message type at the bytes (names-only; the message types
are `PbType`s, `InvProto.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.SizePb

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

axiom proto.SizePb.wp_proof : proto.SizePb.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
