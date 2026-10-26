/-
The trust boundary: `proto.SizeMessage` (`google.golang.org/protobuf/proto` is names-only),
D21 M2 (2026-10-19); see the spec file for the statement and its justification.
-/
module

public import Spec.google_golang_org.protobuf.proto.SizeMessage

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
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The trust boundary**: protobuf-go's `proto` runtime, as the spec states it. -/
axiom proto.SizeMessage.wp_proof : proto.SizeMessage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
