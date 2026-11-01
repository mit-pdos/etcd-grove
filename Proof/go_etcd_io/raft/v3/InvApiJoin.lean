/-
# Raft's node API: joining a cluster of client decisions (2026-10-29, stage U4)

The definitions behind `InvNodeRule.lean`'s sealed `joinAuth`/`nodeJoin`, and the proof of
`joinAuth_join` (`notes/raft-unified-plan.md`, U4; the frozen design's §2, "joining").

**Every node id is allocated at once.** Raft's ghost state names each node's ghost maps in pure maps
fixed at allocation (`RaftNames.reVotes`, ...; the commit invariant holds a vote table over
`reVotes`), and the node API's table of the nodes' views likewise (`Cluster.nodeTab`). Rather than
make those maps grow, `cluster_alloc_dec_impl` allocates them for **every** non-zero id
(`allNodeIds`, a finite set of `2^64 - 1` ids: the allocation is by induction over a set, never
computed), each at raft's initial state (`initPState`: term `0`, an empty log; the cluster's log
starts empty). A founder's token takes its id's part (`nodeFounderU`); the others stay in the join
authority (`joinAuthU γ U`: the parts of the ids outside `U`, the ids started or reserved), from which
`joinAuth_join_impl` takes one out (`nodeJoinU`). A joiner is then, to the protocol, exactly a founder
that has not been started: a node at `c0` with an empty log, which the invariant already admits.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiDec
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The ids `1..n`, as a set (by induction on `n`: nothing is computed). -/
theorem exists_idsUpTo : ∀ n : Nat, n < 2 ^ 64 →
    ∃ S : GSet w64, ∀ x : w64, x ∈ S ↔ (1 ≤ uint.Z x ∧ uint.Z x ≤ (n : Int))
  | 0, _ => ⟨∅, fun x => by rw [GMap.elem_of_empty]; exact ⟨False.elim, fun h => by omega⟩⟩
  | n + 1, h => by
    obtain ⟨S, hS⟩ := exists_idsUpTo n (by omega)
    refine ⟨{[W64 ((n : Int) + 1)]} ∪ S, fun x => ?_⟩
    rw [GMap.elem_of_union, GMap.elem_of_singleton, hS]
    have hz : uint.Z (W64 ((n : Int) + 1)) = (n : Int) + 1 := by word
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · rw [hz]; omega
      · omega
    · rintro ⟨h1, h2⟩
      by_cases hx : uint.Z x = (n : Int) + 1
      · left; rw [← hz] at hx; word
      · right; omega

/-- **Every node id but `0`** (raft's `None`). -/
def allNodeIds : GSet w64 := Classical.choose (exists_idsUpTo (2 ^ 64 - 1) (by omega))

theorem mem_allNodeIds (x : w64) : x ∈ allNodeIds ↔ x ≠ W64 0 := by
  unfold allNodeIds
  rw [Classical.choose_spec (exists_idsUpTo (2 ^ 64 - 1) (by omega)) x]
  have h0 := uint_Z_nonneg x
  have hr := (word.unsigned_range x).2
  constructor
  · rintro ⟨h1, -⟩ h
    rw [h] at h1
    rw [show uint.Z (W64 0) = 0 from rfl] at h1
    omega
  · intro hx
    have hnz : uint.Z x ≠ 0 := fun h => hx (by word)
    omega

section join
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **One node's allocated part** (2026-11-01, durability stage I-7; until then raft's ghost state
of node `id` at the initial state and its table of views, empty): its durable state at
`RaftState.init` and its vacant slot. -/
def joinSlotU (γ : Cluster) (id : w64) : IProp GF :=
  iprop(raftStateU γ id RaftState.init ∗ nodeVacantU γ id)

/-- What every node's `RestartNode` takes besides its part (persistent): the cluster's initial
membership the voters of raft's names (`reCfg`, none of them `0`), the empty log committed and the
term budget. -/
def joinBaseU (γ : Cluster) : IProp GF :=
  iprop(⌜(∃ g, ModeDec γ (Membership.simple γ.raft.reCfg) g) ∧ W64 0 ∉ γ.raft.reCfg⌝ ∗
    isCommitted γ.raft [] ∗ inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 0))

instance joinBaseU_persistent (γ : Cluster) : Persistent (joinBaseU (GF := GF) γ) := by
  unfold joinBaseU; infer_instance

/-- **The join authority** (`InvNodeRule`'s `joinAuth`): the parts of every non-zero id outside
`U`. -/
def joinAuthU (γ : Cluster) (U : GSet w64) : IProp GF :=
  iprop(joinBaseU γ ∗ [∗map] id ↦ _u ∈ toMap (allNodeIds \ U), joinSlotU γ id)

-- (2026-11-01, durability stage I-7) `nodeJoinU` (`nodeJoin`'s body) deleted.

theorem joinAuthU_eq (γ : Cluster) (U U' : GSet w64) (h : ∀ x, x ∈ U ↔ x ∈ U') :
    joinAuthU (GF := GF) γ U = joinAuthU γ U' := by
  rw [GMap.set_eq h]

/-- **Taking a new id's part out of the authority.** -/
theorem joinAuth_join_impl (γ : Cluster) (N : Namespace) (U : GSet w64) (id : w64) :
    id ∉ U → id ≠ W64 0 →
    isClusterU (GF := GF) γ N ∗ joinAuthU γ U ==∗
      joinAuthU γ ({[id]} ∪ U) ∗ raftStateU γ id RaftState.init ∗ nodeVacantU γ id := by
  intro hU hz
  -- PORT(durability stage II): restated (I-7: the id's durable state and slot out)
  sorry

-- (2026-11-01, durability stage I-7) `nodeFounderU` and `nodeJoin_founder_impl` deleted.

/-- Taking out the parts of the distinct ids `vs`, none in `U`, nor `0`. -/
theorem joinAuth_join_list (γ : Cluster) (N : Namespace) (vs : List w64) :
    ∀ (U : GSet w64), vs.Nodup → (∀ x ∈ vs, x ∉ U ∧ x ≠ W64 0) →
    isClusterU (GF := GF) γ N ∗ joinAuthU γ U ==∗
      joinAuthU γ (GMap.listToSet vs ∪ U) ∗ [∗list] id ∈ vs, joinSlotU γ id := by
  -- PORT(durability stage II): restated (I-7: `joinSlotU` in place of `nodeJoinU`)
  sorry

end join

end ApiImpl
end EtcdGrove
end Perennial
