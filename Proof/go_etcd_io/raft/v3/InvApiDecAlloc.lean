/-
# Raft's node API: allocating a cluster of client decisions, with snapshots (2026-10-28)

`cluster_alloc_dec_impl`, behind `InvNodeRule.lean`'s `cluster_alloc` (the conf-change decision switch;
until then `cluster_alloc_rule_impl`, of a rule fixed at allocation): raft's ghost state for the
voters `vs` with an empty log (`ownRaftGhost_alloc_core_reg`), in the dynamic mode of the base decoder
that decides nothing (`noDec`) from the voters' membership, over the client's decision map (an empty
ghost map, allocated first: `RaftNames.reDec`), outside the no-snapshot mode (`ns = false`, which the
empty log allows), with every snapshot's data admitted and a registry of the snapshots made (an empty
`mono_list`, allocated first); leader transfer on (the no-transfer mode needs a bootstrap log).
(2026-10-29, stage U4) Raft's ghost state and the node table for **every** non-zero id
(`allNodeIds`, `InvApiJoin.lean`): the founders' parts go to their tokens, the others stay in the
join authority (`joinAuthU γ (listToSet vs)`), for joiners.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiJoin
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A new cluster of client decisions**, of the voters `vs`, with snapshots (`InvNodeRule`'s
`cluster_alloc`). -/
theorem cluster_alloc_dec_impl (N : Namespace) (vs : List w64) (dup : Bool) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ⌜γ.raft.dup = dup ∧ γ.raft.reBoot.length = 0⌝ ∗ ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗
        isClusterU γ N ∗ ownConfDecisionsU γ ∅ ∗
        confAtU γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMadeU γ [] ∗
        joinAuthU γ (GMap.listToSet vs) ∗
        [∗list] id ∈ vs, raftStateU γ id RaftState.init ∗ nodeVacantU γ id := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

end alloc

end ApiImpl
end EtcdGrove
end Perennial
