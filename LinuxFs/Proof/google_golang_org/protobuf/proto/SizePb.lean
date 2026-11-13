/-
The copy for the part `LinuxFs/` of `Proof/google_golang_org/protobuf/proto/SizePb.lean`: the same
trust-boundary axiom, over the part's copy of the spec. Its header follows.
-/
/-
The trust boundary: `proto.SizePb.spec` (names-only; registered message types at their wire content,
`InvProto.lean`; per-type models, stage A, CP2).
-/
module

public import LinuxFs.Spec.google_golang_org.protobuf.proto.SizePb

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

axiom proto.SizePb.wp_proof : proto.SizePb.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
