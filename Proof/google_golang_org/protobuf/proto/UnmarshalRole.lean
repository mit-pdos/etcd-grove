/-
The trust boundary: `proto.Unmarshal` of an `authpb.Role` (names-only; the encoding is opaque,
`auth/Buckets.lean`). The auth plan's S1 (2026-10-23).
-/
module

public import Spec.google_golang_org.protobuf.proto.UnmarshalRole

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

axiom proto.UnmarshalRole.wp_proof : proto.UnmarshalRole.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
