/-
The trust boundary: `proto.Clone` of any message type (names-only; the message types are
`PbType`s, `InvProto.lean`).
-/
module

public import Spec.google_golang_org.protobuf.proto.ClonePb

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

axiom proto.ClonePb.wp_proof : proto.ClonePb.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
