/-
The trust boundary: `proto.MarshalConfChange` (`google.golang.org/protobuf/proto` is names-only), raft v3.7
retarget, stage R1; see the spec file for the statement and its justification.
-/
module

public import RaftWitness.Spec.google_golang_org.protobuf.proto.MarshalConfChange

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
axiom proto.MarshalConfChange.wp_proof : proto.MarshalConfChange.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
