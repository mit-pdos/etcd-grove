/-
The trust boundary: `proto.SizeMessage` (`google.golang.org/protobuf/proto` is names-only), of a
`*pb.Message` (branch pr-verify/etcd-21569: `snap.NewMessage`); see the spec file for the statement and its justification.
-/
module

public import Spec.google_golang_org.protobuf.proto.SizeMessage

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
axiom proto.SizeMessage.wp_proof : proto.SizeMessage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
