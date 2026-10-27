/-
The trust boundary: protoc-gen-go's generated `ConfChangeType.String` (names-only in the raft v3.7
translation); the old proof's axiom restated (2026-10-15, raft v3.7 retarget, stage R2). See the
spec for the reading of `raft.pb.go` it encodes.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an assumption
under `#print axioms`. -/
axiom raftpb.ConfChangeType.String.wp_proof :
  raftpb.ConfChangeType.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
