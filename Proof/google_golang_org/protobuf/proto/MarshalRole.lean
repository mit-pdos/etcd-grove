/-
The trust boundary: `proto.Marshal` of an `authpb.Role` (names-only; the encoding is opaque,
`auth/Buckets.lean`), the twin of `proto.UnmarshalRole`. auth-schema-srv A3 (2026-11-17; Draft
`notes/auth-schema-srv-a3-draft.md`, attack `notes/axiom-review/auth-a3-marshal.md`).
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalRole

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

axiom proto.MarshalRole.wp_proof : proto.MarshalRole.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
