/-
The trust boundary: `proto.Clone` (`google.golang.org/protobuf/proto` is names-only), for a
`*pb.Compare`.
-/
module

public import Spec.google_golang_org.protobuf.proto.Clone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- **The trust boundary**: protobuf's `proto.Clone` (names-only: Goose does not translate
protobuf's reflection) deep-copies a `*pb.Compare` into a fresh message with the same contents, and clones a nil
`*raftpb.Snapshot` into a nil one. -/
axiom proto.Clone.wp_proof : proto.Clone.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
