/-
The trust boundary: gogoproto's generated `(*ConfChangeV2).Marshal` (names-only); see the spec for the reading
of `raft.pb.go` it encodes.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__Marshal

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
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an assumption
under `#print axioms`. -/
axiom raftpb.ConfChangeV2.Marshal.wp_proof : raftpb.ConfChangeV2.Marshal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
