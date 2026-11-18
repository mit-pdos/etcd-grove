/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneEntry.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.CloneEntry

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

-- raft-noax: TODO prove `raftpb.CloneEntry` (`raftpb/noax.go`) against its spec.
theorem raftpb.CloneEntry.wp_proof : raftpb.CloneEntry.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
