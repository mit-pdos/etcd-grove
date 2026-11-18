/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/marshalConfChangeSingle.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.marshalConfChangeSingle
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.appendEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.appendVarint

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

theorem raftpb.marshalConfChangeSingle.wp_proof
    (wp_appendEnum : raftpb.appendEnum.spec (GF := GF) (hG := hG))
    (wp_appendVarint : raftpb.appendVarint.spec (GF := GF) (hG := hG)) :
    raftpb.marshalConfChangeSingle.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
