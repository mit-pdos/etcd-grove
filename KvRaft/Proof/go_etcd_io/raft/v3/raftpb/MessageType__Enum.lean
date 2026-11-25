-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/MessageType__Enum.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/MessageType__Enum.lean`.
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

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

theorem raftpb.MessageType.Enum.wp_proof :
    raftpb.MessageType.Enum.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
