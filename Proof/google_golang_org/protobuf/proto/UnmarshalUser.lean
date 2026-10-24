/-
The trust boundary: `proto.Unmarshal` of an `authpb.User` (names-only; the encoding is opaque,
`auth/Buckets.lean`). The auth plan's S1 (2026-10-23).
-/
module

public import Spec.google_golang_org.protobuf.proto.UnmarshalUser

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

axiom proto.UnmarshalUser.wp_proof : proto.UnmarshalUser.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
