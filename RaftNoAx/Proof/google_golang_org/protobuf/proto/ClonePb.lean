-- The copy for the part `RaftNoAx/` of `Proof/google_golang_org/protobuf/proto/ClonePb.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The trust boundary: `proto.ClonePb.spec` (names-only; registered message types at their wire content,
`InvProto.lean`; per-type models, stage A, CP2).
-/
module

public import RaftNoAx.Spec.google_golang_org.protobuf.proto.ClonePb

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
