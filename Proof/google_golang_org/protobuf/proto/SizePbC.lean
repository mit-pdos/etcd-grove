/-
The trust boundary: `proto.SizePbC.spec` (names-only; registered message types at their wire content,
`InvProto.lean`; per-type models, stage A, CP2).
-/
module

public import Spec.google_golang_org.protobuf.proto.SizePbC

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

axiom proto.SizePbC.wp_proof : proto.SizePbC.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
