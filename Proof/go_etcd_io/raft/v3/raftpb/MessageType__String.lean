/-
The trust boundary: protoc-gen-go's generated `MessageType.String` (names-only in the raft v3.7
translation), as `MessageType.String`'s (2026-10-23, rafthttp stage 5c).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an assumption
under `#print axioms`. -/
axiom raftpb.MessageType.String.wp_proof :
  raftpb.MessageType.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
