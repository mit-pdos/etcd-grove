-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNode__HasReady.lean` (etc/copy-part.py; rerun it, do not edit).
/- Port of election_proof/proof_RawNode__HasReady.v (857d09190).

(#33 S4, P-raft-3) The proof is the strengthened triple's, `RawNode.HasReady.wp_absProof`
(`RawNode__HasReadyAbs.lean`, where this file's proof moved, over `ownRawNodeAt`); the old spec is its
corollary (`RawNode.HasReady.spec_of_abs`, `RawNodeSpecOfAbs.lean`). One proof.

Until then: since 2026-10-09 the spec pins nothing about the answer, so every path returns the same
way (close the raft struct's view unchanged and refold `ownRawNode`); raft v3.7 (2026-10-16, stage
R5): `r.softState()` and `r.hardState()` are called through their specs on the closed struct. -/
module

public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import KvNet.Proof.go_etcd_io.raft.v3.RawNode__HasReadyAbs
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeSpecOfAbs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.HasReady.wp_proof
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableEnts : raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextCommittedEnts :
      raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_raft_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_raft_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    RawNode.HasReady.spec (GF := GF) (hG := hG) :=
  RawNode.HasReady.spec_of_abs (RawNode.HasReady.wp_absProof wp_SoftState_equal wp_IsEmptyHardState
    wp_isHardStateEqual wp_raftLog_hasNextUnstableSnapshot wp_raftLog_hasNextUnstableEnts
    wp_raftLog_hasNextCommittedEnts wp_raft_softState wp_raft_hardState)

end proof

end EtcdGrove
end Perennial
