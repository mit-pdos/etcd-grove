/-
`proto.Equal` of two `*spb.Status`: protobuf's `proto` is names-only and `Equal` works by
reflection (see the spec): an axiom. Lean-first (no Rocq counterpart). Review:
`notes/axiom-review/proto-equal-status.md`.
-/
module

public import Spec.google_golang_org.protobuf.proto.EqualStatus

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
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- protobuf's `proto` is not translated; see the comment at the spec. -/
axiom proto.EqualStatus.wp_proof : proto.EqualStatus.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
