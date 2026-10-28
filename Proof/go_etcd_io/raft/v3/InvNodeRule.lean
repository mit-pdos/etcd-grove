/-
# Raft's node API: a cluster with snapshots and reconfiguration (2026-10-28, stage U4a)

The interim of the unified node API (`notes/raft-unified-plan.md`, stage U4a): a cluster in raft's
dynamic mode **and** outside its no-snapshot mode, its conf entries decided by a rule fixed at
allocation (`ConfRule`, `cluster_alloc_rule`). Candidate 13's decisions
(`notes/spec-first-study/raft-node-unified-candidate-13.md`, section 13) will replace the rule under
these statements: the rule appears only in the allocation and in `confPolicy` (the stand-in for
candidate 13's `confPolicyInv`, a client library over the one-shot decision tokens); the specs and the
other laws are in candidate 13's shapes (`confAt`, `confDecided`, `ConfDecision`).

Every predicate is **sealed** over its definition in `InvApiRule.lean` (laws and allocation proved
there, `InvApiRuleAlloc.lean`); nothing here is `sorry`. The node's other predicates are
`InvNode`'s (`isNode`, `nodeDriver`, `nodeConfig`, `deliveredLogLb`, `snapshotCert`, ...), the specs
over this cluster `RestartNode.unifiedSpec`, `node.ApplyConfChange.unifiedSpec`,
`node.Advance.unifiedSpec`.

- **The cluster** (`isCluster`, persistent): its nodes' configuration the membership after their
  applied conf entries, from the voters' membership, each decided once for all nodes; snapshots taken
  and installed.
- **The configuration** (`confAt γ k m`, persistent): the membership after the first `k` committed
  entries is `m`; `confDecided γ k d`: the conf entry at position `k` was decided `d` (apply a change,
  or skip it). A client tracks `confAt` beside its node's view (`nodeConfig`): past entries that are no
  conf change (`confAt_noConf`), past a decided one (`confAt_decided`); a decision from the cluster's
  rule (`confPolicy_decide`).
- **Snapshots** (TaDa style): the client's registry of the snapshots it made (`ownSnapsMade`, from the
  allocation, empty), `snapshotCert_make` (a committed prefix at its configuration), `snapshotCert_made`
  (a certificate's prefix, configuration and record), `snapMade_elem`.
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
import Proof.go_etcd_io.raft.v3.InvApiRule
import Proof.go_etcd_io.raft.v3.InvApiRuleAlloc
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The cluster -/

/-- **A cluster with snapshots and reconfiguration** (persistent; stage U4a: raft's dynamic mode of
the rule the cluster was allocated with, outside the no-snapshot mode, with the registry of the
snapshots made). -/
@[no_expose] def isCluster (γ : Cluster) (N : Namespace) : IProp GF := ApiImpl.isClusterU γ N

instance isCluster_persistent (γ : Cluster) (N : Namespace) :
    Persistent (isCluster (GF := GF) γ N) := by
  unfold isCluster; exact ApiImpl.isClusterU_persistent γ N

/-- **The membership after the first `k` committed entries is `m`** (persistent): every conf entry
among them decided. -/
@[no_expose] def confAt (γ : Cluster) (k : Nat) (m : Membership) : IProp GF :=
  ApiImpl.confAtU γ k m

instance confAt_persistent (γ : Cluster) (k : Nat) (m : Membership) :
    Persistent (confAt (GF := GF) γ k m) := by
  unfold confAt; exact ApiImpl.confAtU_persistent γ k m

/-- **The conf entry at position `k` (index `k + 1`) of the committed log was decided `d`**
(persistent). -/
@[no_expose] def confDecided (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF :=
  ApiImpl.confDecidedU γ k d

instance confDecided_persistent (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Persistent (confDecided (GF := GF) γ k d) := by
  unfold confDecided; exact ApiImpl.confDecidedU_persistent γ k d

/-- (interim, stage U4a) **The cluster decides its conf entries by the rule `r`** (persistent): the
rule fixed at allocation (`cluster_alloc_rule`), in place of candidate 13's client-owned decision
tokens with a `confPolicyInv` over them. -/
@[no_expose] def confPolicy (γ : Cluster) (r : ConfRule) : IProp GF := ApiImpl.confPolicyU γ r

instance confPolicy_persistent (γ : Cluster) (r : ConfRule) :
    Persistent (confPolicy (GF := GF) γ r) := by
  unfold confPolicy; exact ApiImpl.confPolicyU_persistent γ r

/-- **The snapshots the client made** (exclusive): the records `S`, in the cluster's registry. -/
@[no_expose] def ownSnapsMade (γ : Cluster) (S : List SnapRec) : IProp GF := ApiImpl.ownSnapsMadeU γ S

/-- No later credit to open an invariant holding it. -/
instance ownSnapsMade_timeless (γ : Cluster) (S : List SnapRec) :
    Timeless (ownSnapsMade (GF := GF) γ S) := by
  unfold ownSnapsMade; exact ApiImpl.ownSnapsMadeU_timeless γ S

/-- **The snapshot `s` was made** (persistent). -/
@[no_expose] def snapMade (γ : Cluster) (s : SnapRec) : IProp GF := ApiImpl.snapMadeU γ s

instance snapMade_persistent (γ : Cluster) (s : SnapRec) :
    Persistent (snapMade (GF := GF) γ s) := by
  unfold snapMade; exact ApiImpl.snapMadeU_persistent γ s

/-- **A founder's boot token** (exclusive): node `id` of a new cluster of the voters `vs`, for its
`RestartNode` on an empty storage whose `InitialState` names the voters
(`RestartNode.unifiedSpec`). -/
@[no_expose] def nodeFounder (γ : Cluster) (N : Namespace) (vs : List w64) (id : w64) : IProp GF :=
  ApiImpl.nodeFounderU γ N vs id

/-- **A new cluster of the voters `vs`, its conf entries decided by the rule `r`** (stage U4a), in the
caller's namespace `N`: nothing committed, the read contexts with none used, the read credits, the
cluster (with snapshots), its rule, the membership of no entry the voters', the registry of the
snapshots made (empty), leader transfer on, and one founder's token per voter. The term budget,
backed by time receipts (`receiptBound`), is the cluster's. No premise on the rule: a decision is
taken only where its result is a membership (`confPolicy_decide`). -/
theorem cluster_alloc_rule (N : Namespace) (vs : List w64) (r : ConfRule) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isCluster γ N ∗ confPolicy γ r ∗ confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
        ownSnapsMade γ [] ∗ leaderTransferOn γ N ∗
        [∗list] id ∈ vs, nodeFounder γ N vs id := by
  intro Hrb Hne Hnd Hnz Hlen
  unfold ownCommittedOps ownReadCtxs readCredits isCluster confPolicy confAt ownSnapsMade
    leaderTransferOn nodeFounder
  exact ApiImpl.cluster_alloc_rule_impl N vs r E Hrb Hne Hnd Hnz Hlen

/-! ## The configuration -/

theorem confAt_agree (γ : Cluster) (k : Nat) (m1 m2 : Membership) :
    confAt (GF := GF) γ k m1 ∗ confAt γ k m2 ⊢ ⌜m1 = m2⌝ := by
  unfold confAt; exact ApiImpl.confAt_agree_impl γ k m1 m2

theorem confAt_valid (γ : Cluster) (k : Nat) (m : Membership) :
    confAt (GF := GF) γ k m ⊢ ⌜m.Valid⌝ := by
  unfold confAt; exact ApiImpl.confAt_valid_impl γ k m

/-- **Past entries that are no conf change** (candidate 13's `confAt_normal`, over a range). -/
theorem confAt_noConf (γ : Cluster) (l : List LogEntry) (a b : Nat) (m : Membership) :
    NoConfChangeIn l a b → a ≤ b → b ≤ l.length →
    isCommittedLogLb (GF := GF) γ l ∗ confAt γ a m ⊢ confAt γ b m := by
  intro hn hab hb
  unfold isCommittedLogLb confAt; exact ApiImpl.confAt_noConf_impl γ l a b m hn hab hb

/-- **Past a decided conf entry**: the decision's result. -/
theorem confAt_decided (γ : Cluster) (k : Nat) (m : Membership) (d : ConfDecision) :
    confAt (GF := GF) γ k m ∗ confDecided γ k d ⊢
      ∃ m', ⌜d.step m = some m'⌝ ∗ confAt γ (k + 1) m' := by
  unfold confAt confDecided; exact ApiImpl.confAt_decided_impl γ k m d

/-- (interim, stage U4a) **The cluster's decision** on the committed conf entry `e` at position `k`,
where the membership is `m`: the rule's answer there (its change applied, its `none` a skip), given
that it has a result (candidate 13's `confPolicy_decide`). -/
theorem confPolicy_decide (γ : Cluster) (r : ConfRule) (l : List LogEntry) (k : Nat) (e : LogEntry)
    (m m' : Membership) :
    l[k]? = some e → e.isConfChange →
    (ConfDecision.ofRule (r (l.take k) m e)).step m = some m' →
    confPolicy (GF := GF) γ r ∗ isCommittedLogLb γ l ∗ confAt γ k m ⊢
      confDecided γ k (ConfDecision.ofRule (r (l.take k) m e)) := by
  intro he hc hs
  unfold confPolicy isCommittedLogLb confAt confDecided
  exact ApiImpl.confPolicy_decide_impl γ r l k e m m' he hc hs

/-! ## Snapshots -/

/-- **A snapshot made is one of the client's.** -/
theorem snapMade_elem (γ : Cluster) (S : List SnapRec) (s : SnapRec) :
    ownSnapsMade (GF := GF) γ S ∗ snapMade γ s ⊢ ⌜s ∈ S⌝ := by
  unfold ownSnapsMade snapMade; exact ApiImpl.snapMade_elem_impl γ S s

/-- **Certifying a snapshot of a committed prefix** `l` (its length `i`, last term `t`) at the
membership `m` after it (`confAt`), its `ConfState` `cs` reporting `m`, its data `d` anything: the
snapshot is recorded as made. A fancy update inside `N` (it opens raft's commit invariant); the
lists' well-formedness raft's `restore` needs (`SnapListsOk`: ids nonzero, at most `2^62` entries in
all, the index below `2^61`) a premise (`notes/decisions.md`, "Stages U2, U3"). -/
theorem snapshotCert_make (γ : Cluster) (N : Namespace) (E : CoPset) (l : List LogEntry) (i t : w64)
    (d : List w8) (m : Membership) (cs : ConfStateM) (S : List SnapRec) :
    ↑N ⊆ E → l.length = uint.nat i → Option.map LogEntry.term l.getLast? = some t →
    SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ → confStateIs cs m →
    ⊢ isCluster (GF := GF) γ N -∗ isCommittedLogLb γ l -∗ confAt γ l.length m -∗
      ownSnapsMade γ S ={E}=∗
      ownSnapsMade γ (S ++ [⟨l.length, m, d⟩]) ∗
      snapshotCert γ N ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ := by
  intro HE Hlen Hlast Hok Hcs
  unfold isCluster isCommittedLogLb confAt ownSnapsMade snapshotCert
  exact ApiImpl.snapshotCert_make_impl γ N E HE l i t d m cs S Hlen Hlast Hok Hcs

/-- **What a certificate says**: the snapshot is of a committed prefix of its length and last term,
at the membership after it (which its lists and auto-leave flag report), and was made. -/
theorem snapshotCert_made (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    isCluster (GF := GF) γ N ∗ snapshotCert γ N k ⊢
      ∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAt γ l.length m ∗
        snapMade γ ⟨l.length, m, k.dat⟩ ∗
        ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
          k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  unfold isCluster isCommittedLogLb confAt snapMade snapshotCert
  exact ApiImpl.snapshotCert_made_impl γ N k

end api

end EtcdGrove
end Perennial
