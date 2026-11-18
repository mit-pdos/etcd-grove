/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV2.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- raft-noax: TODO prove `raftpb.UnmarshalConfChangeV2` (`raftpb/noax.go`) against its spec.
theorem raftpb.UnmarshalConfChangeV2.wp_proof : raftpb.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
