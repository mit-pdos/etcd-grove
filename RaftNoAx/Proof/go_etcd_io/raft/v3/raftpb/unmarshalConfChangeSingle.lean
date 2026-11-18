/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/unmarshalConfChangeSingle.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

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

theorem raftpb.unmarshalConfChangeSingle.wp_proof
    (wp_consumeEnum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.unmarshalConfChangeSingle.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
