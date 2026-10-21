/-
The trust boundary: `proto.MarshalConfChangeV2` (`google.golang.org/protobuf/proto` is names-only), raft v3.7
retarget, stage R1; see the spec file for the statement and its justification.
-/
module

public import RaftWitness.Spec.google_golang_org.protobuf.proto.MarshalConfChangeV2

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
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The trust boundary**: protobuf-go's `proto` runtime, as the spec states it. -/
axiom proto.MarshalConfChangeV2.wp_proof : proto.MarshalConfChangeV2.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
