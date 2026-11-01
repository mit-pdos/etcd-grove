/-
# Raft's node API: a new cluster with a bootstrap log (2026-10-30, stage R5)

The definitions behind `InvNodeRule.lean`'s sealed `nodeBoot`, and `cluster_alloc_boot_impl`, the
bootstrap-log form of `cluster_alloc` (its empty-log form is `cluster_alloc_dec_impl`,
`InvApiDecAlloc.lean`): the cluster of client decisions of `InvApiDec.lean` (raft's dynamic mode of the
base decoder that decides nothing, from the voters' membership, with snapshots and a registry of them),
whose committed log starts with the bootstrap log `boot` -- one `AddNode` per voter, as raft's
`Bootstrap` writes it (`BootLog`) -- and whose nodes start at the bootstrap state (`bootPState`: term
`1`, the log `boot` committed), for `StartNode` (`nodeBootU`: the node's part, the boot log's bytes,
`bootMarshal`, and the term budget at the bootstrap term). The boot conf entries are not decided here:
the client decides them as any committed conf entry (`confDecide`).

No join authority: every node is allocated at the bootstrap state, and raft's protocol keeps the
bootstrap log a prefix of every node's log (`Protocol/Ghost.lean`), which a newcomer's `RestartNode` on
an empty storage would not be.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiJoin
public import Proof.go_etcd_io.raft.v3.InvBoot
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A founder's start token in a cluster with a bootstrap log** (`InvNodeRule`'s `nodeBoot`): node
`id`, one of the voters `ps`, of the cluster; raft's names those of the voters' membership and of the
bootstrap log of the peers `ps` (`BootLogOk`), whose bytes are `Marshal`'s at the peers' changes with
the contexts `ctxs` (`bootMarshal`), committed; the term budget at the bootstrap term. (2026-11-01,
durability stage I-7: persistent; until then also the node's raft ghost state at the bootstrap state
and its (empty) table of views, which moved to `raftStateU`/`nodeVacantU`.) -/
def nodeBootU (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (id : w64) :
    IProp GF :=
  iprop(isClusterU γ N ∗
    ⌜id ∈ ps ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) < 2 ^ 62 ∧
      γ.raft.reCfg = GMap.listToSet ps ∧
      (∃ g, ModeDec γ (Membership.simple (GMap.listToSet ps)) g) ∧ BootLogOk ps γ.raft.reBoot⌝ ∗
    bootMarshal ps ctxs γ.raft.reBoot ∗ isCommitted γ.raft γ.raft.reBoot ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 1))

instance nodeBootU_persistent (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (id : w64) : Persistent (nodeBootU (GF := GF) γ N ps ctxs id) := by
  unfold nodeBootU; infer_instance

/-- No entry of a bootstrap log is an empty `ConfChangeV2` (each is a `ConfChange`, type `1`). -/
theorem bootLogOk_noEmptyV2 {ps : List w64} {L : List EntryM} (H : BootLogOk ps L) :
    ∀ x ∈ L, ¬ IsEmptyV2 x := by
  rintro x hx ⟨_, h⟩
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  obtain ⟨-, -, Hty, -⟩ := H.2.2 k x hk
  rw [Hty] at h
  have := congrArg (fun x : w32 => uint.Z x) h
  revert this; decide

/-- **A new cluster of client decisions with a bootstrap log**, of the voters `vs` (`InvNodeRule`'s
`cluster_alloc` at a non-empty `boot`). -/
theorem cluster_alloc_boot_impl (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (dup : Bool) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    BootLog vs ctxs boot →
    ⊢ bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0) ={E}=∗ ∃ γ,
        ⌜γ.raft.dup = dup ∧ γ.raft.reBoot.length = boot.length⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isClusterU γ N ∗ ownConfDecisionsU γ ∅ ∗
        confAtU γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMadeU γ [] ∗
        isCommittedLogLb γ boot ∗
        [∗list] id ∈ vs, nodeBootU γ N vs ctxs id ∗ raftStateU γ id RaftState.init ∗
          nodeVacantU γ id := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

end boot

end ApiImpl
end EtcdGrove
end Perennial
