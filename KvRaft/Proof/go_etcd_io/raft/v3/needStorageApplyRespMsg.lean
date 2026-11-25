-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/needStorageApplyRespMsg.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Port of `election_proof/proof_needStorageApplyRespMsg.v` (857d09190).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.needStorageApplyRespMsg
public import KvRaft.Spec.go_etcd_io.raft.v3.needStorageApplyMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem needStorageApplyRespMsg.wp_proof
    (wp_needStorageApplyMsg : needStorageApplyMsg.spec (GF := GF) (hG := hG)) :
    needStorageApplyRespMsg.spec (GF := GF) (hG := hG) := by
  intro rd
  wp_start as -
  wp_auto
  wp_apply wp_needStorageApplyMsg
  iapply HΦ
  ipureintro
  trivial

end proof

end EtcdGrove
end Perennial
