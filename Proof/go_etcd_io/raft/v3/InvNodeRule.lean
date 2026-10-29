/-
# Raft's node API: a cluster with snapshots and reconfiguration, its conf entries decided by the client

(2026-10-28, stage U4a; the conf-change decision switch, `notes/spec-first-study/raft-decisions-spec.md`,
§1, §3, §4.) A cluster in raft's dynamic mode **and** outside its no-snapshot mode, whose committed conf
entries the client decides: a client-owned authority over the decisions (`ownConfDecisions`, from the
allocation, empty), one decision per position (`confDecide`), every node's configuration the fold of the
decisions over the committed log. Raft's API mentions no rule: a client deciding by a rule uses the
library `ConfPolicy.lean` over the authority. (Until the switch, stage U4a's interim: a rule fixed at
allocation, `cluster_alloc_rule`, with raft's persistent `confPolicy`.)

Every predicate is **sealed** over its definition in `InvApiDec.lean` (laws and allocation proved
there, `InvApiDecAlloc.lean`); nothing here is `sorry`. The node's other predicates are `InvNode`'s
(`isNode`, `nodeDriver`, `nodeConfig`, `deliveredLogLb`, `snapshotCert`, ...), the specs over this cluster
`RestartNode.unifiedSpec`, `node.ApplyConfChange.unifiedSpec`, `node.Advance.unifiedSpec`.

- **The cluster** (`isCluster`, persistent): its nodes' configuration the membership after their
  applied conf entries, from the voters' membership, each decided once for all nodes; snapshots taken
  and installed.
- **Decisions**: `ownConfDecisions γ D` (exclusive, timeless), the decisions recorded so far by
  position; `confDecided γ k d` (persistent), that the conf entry at position `k` was decided `d`
  (`_lookup`, `_witness`, `confDecided_agree`); `confDecide` records a decision on an undecided
  committed conf entry, at the configuration before it, with a result.
- **The configuration** (`confAt γ k m`, persistent): the membership after the first `k` committed
  entries is `m`. A client tracks `confAt` beside its node's view (`nodeConfig`): past entries that are
  no conf change (`confAt_noConf`), past a decided one (`confAt_decided`). `skippedIn γ l a b`: every
  conf entry of `l` in `[a, b)` decided `.skip`, what `ApplyConfChange`/`Advance` take for the entries
  their view passes.
- **Snapshots** (TaDa style): the client's registry of the snapshots it made (`ownSnapsMade`, from the
  allocation, empty), `snapshotCert_make` (a committed prefix at its configuration), `snapshotCert_made`
  (a certificate's prefix, configuration and record), `snapMade_elem`.
- **Joining** (2026-10-29, stage U4): the ids started or reserved (`joinAuth γ U`, from the allocation
  at the founders), and a newcomer's token (`nodeJoin γ N id`, `joinAuth_join`), for its `RestartNode`
  at the initial membership with an empty log, as a founder's.
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiDecAlloc
import Proof.go_etcd_io.raft.v3.InvApiJoin
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

/-- **A cluster with snapshots and reconfiguration** (persistent): raft's dynamic mode of the client's
decisions, outside the no-snapshot mode, with the registry of the snapshots made. -/
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

/-- (2026-10-28, the decision switch) No later credit to open an invariant holding it
(`ConfPolicy.lean`). -/
instance confAt_timeless (γ : Cluster) (k : Nat) (m : Membership) :
    Timeless (confAt (GF := GF) γ k m) := by
  unfold confAt; exact ApiImpl.confAtU_timeless γ k m

/-- **The conf entry at position `k` (index `k + 1`) of the committed log was decided `d`**
(persistent). -/
@[no_expose] def confDecided (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF :=
  ApiImpl.confDecidedU γ k d

instance confDecided_persistent (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Persistent (confDecided (GF := GF) γ k d) := by
  unfold confDecided; exact ApiImpl.confDecidedU_persistent γ k d

instance confDecided_timeless (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Timeless (confDecided (GF := GF) γ k d) := by
  unfold confDecided; exact ApiImpl.confDecidedU_timeless γ k d

/-- **The decisions recorded so far, by log position** (exclusive; the client's, typically in an
invariant). -/
@[no_expose] def ownConfDecisions (γ : Cluster) (D : GMap Nat ConfDecision) : IProp GF :=
  ApiImpl.ownConfDecisionsU γ D

instance ownConfDecisions_timeless (γ : Cluster) (D : GMap Nat ConfDecision) :
    Timeless (ownConfDecisions (GF := GF) γ D) := by
  unfold ownConfDecisions; exact ApiImpl.ownConfDecisionsU_timeless γ D

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

/-- **The ids started or reserved** (exclusive): every node id in `U` has had its token taken
(a founder's or a joiner's); the others' are here. -/
@[no_expose] def joinAuth (γ : Cluster) (U : GSet w64) : IProp GF := ApiImpl.joinAuthU γ U

/-- **A newcomer's token** (exclusive): node `id`, not a founder, for its `RestartNode` on an empty
storage whose `InitialState` names the initial membership's voters (`RestartNode.unifiedSpec`). -/
@[no_expose] def nodeJoin (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  ApiImpl.nodeJoinU γ N id

/-- **A new cluster of the voters `vs`** (§3 of the decision switch, `cluster_alloc` there: the name is
the static cluster's, `InvNode`; until the switch `cluster_alloc_rule`, of a rule), in the caller's
namespace `N`: nothing committed, the read contexts with none used, the read credits, the cluster (with snapshots), the authority over its decisions,
none recorded, the membership of no entry the voters', the registry of the snapshots made (empty),
leader transfer on, the join authority at the voters (2026-10-29, stage U4), and one founder's token
per voter. The term budget, backed by time receipts (`receiptBound`), is the cluster's. -/
theorem cluster_alloc_dec (N : Namespace) (vs : List w64) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isCluster γ N ∗ ownConfDecisions γ ∅ ∗ confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
        ownSnapsMade γ [] ∗ leaderTransferOn γ N ∗ joinAuth γ (GMap.listToSet vs) ∗
        [∗list] id ∈ vs, nodeFounder γ N vs id := by
  intro Hrb Hne Hnd Hnz Hlen
  unfold ownCommittedOps ownReadCtxs readCredits isCluster ownConfDecisions confAt ownSnapsMade
    leaderTransferOn joinAuth nodeFounder
  exact ApiImpl.cluster_alloc_dec_impl N vs E Hrb Hne Hnd Hnz Hlen

/-! ## Joining -/

/-- **Reserving a new id**: its token, out of the authority. -/
theorem joinAuth_join (γ : Cluster) (N : Namespace) (U : GSet w64) (id : w64) :
    id ∉ U → id ≠ W64 0 →
    isCluster (GF := GF) γ N ∗ joinAuth γ U ==∗ joinAuth γ ({[id]} ∪ U) ∗ nodeJoin γ N id := by
  intro hU hz
  unfold isCluster joinAuth nodeJoin
  exact ApiImpl.joinAuth_join_impl γ N U id hU hz

/-! ## Stopped nodes (2026-10-29, stage U9a) -/

/-- **A running node has not stopped**: a holder of a share of `nodeRunning` refutes the stopped
answers (`node.Advance`'s and `node.ApplyConfChange`'s stopped cases). -/
theorem nodeRunning_stopped (n : Loc) (γ : Cluster) (N : Namespace) (q : Qp) :
    isCluster (GF := GF) γ N ∗ nodeRunning n γ N q ∗ nodeStopped n γ N ⊢ False := by
  unfold isCluster nodeRunning nodeStopped
  iintro ⟨-, H⟩
  iapply ApiImpl.nodeRunning_stopped_impl n γ N q $$ H

/-! ## Decisions -/

theorem ownConfDecisions_excl (γ : Cluster) (D1 D2 : GMap Nat ConfDecision) :
    ownConfDecisions (GF := GF) γ D1 ∗ ownConfDecisions γ D2 ⊢ False := by
  unfold ownConfDecisions; exact ApiImpl.ownConfDecisions_excl_impl γ D1 D2

theorem ownConfDecisions_lookup (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    ownConfDecisions (GF := GF) γ D ∗ confDecided γ k d ⊢ ⌜D !! k = some d⌝ := by
  unfold ownConfDecisions confDecided; exact ApiImpl.ownConfDecisions_lookup_impl γ D k d

/-- A recorded decision's witness (the authority given back). -/
theorem ownConfDecisions_witness (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    D !! k = some d →
    ownConfDecisions (GF := GF) γ D ⊢ ownConfDecisions γ D ∗ confDecided γ k d := by
  intro h
  unfold ownConfDecisions confDecided; exact ApiImpl.ownConfDecisions_witness_impl γ D k d h

/-- Two decisions of one position agree (without the authority). -/
theorem confDecided_agree (γ : Cluster) (k : Nat) (d1 d2 : ConfDecision) :
    confDecided (GF := GF) γ k d1 ∗ confDecided γ k d2 ⊢ ⌜d1 = d2⌝ := by
  unfold confDecided; exact ApiImpl.confDecided_agree_impl γ k d1 d2

/-- **Deciding an undecided committed conf entry**, at the configuration before it, with an allowed
decision: one shot per position (the map grows only where it is undefined). -/
theorem confDecide (γ : Cluster) (N : Namespace) (D : GMap Nat ConfDecision) (l : List LogEntry)
    (k : Nat) (e : LogEntry) (m m' : Membership) (d : ConfDecision) :
    D !! k = none → l[k]? = some e → e.isConfChange → d.step m = some m' →
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ∗ ownConfDecisions γ D ==∗
      ownConfDecisions γ (D.insert k d) ∗ confDecided γ k d ∗ confAt γ (k + 1) m' := by
  intro hD he hc hs
  unfold isCluster isCommittedLogLb confAt ownConfDecisions confDecided
  exact ApiImpl.confDecide_impl γ N D l k e m m' d hD he hc hs

/-! ## The configuration -/

theorem confAt_agree (γ : Cluster) (k : Nat) (m1 m2 : Membership) :
    confAt (GF := GF) γ k m1 ∗ confAt γ k m2 ⊢ ⌜m1 = m2⌝ := by
  unfold confAt; exact ApiImpl.confAt_agree_impl γ k m1 m2

theorem confAt_valid (γ : Cluster) (k : Nat) (m : Membership) :
    confAt (GF := GF) γ k m ⊢ ⌜m.Valid⌝ := by
  unfold confAt; exact ApiImpl.confAt_valid_impl γ k m

/-- **Every committed conf entry decodes** (2026-10-29, stage U5): the leader decodes every conf
entry it appends (`raft.go:1320`, raft's own automatic leave by `ccDecodeV2_nil`), so an application
that decodes a committed one never fails. -/
theorem committed_confDecodes (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ⊢
      ⌜∀ e ∈ l, e.isConfChange → ConfEntryDecodes e⌝ := by
  unfold isCluster isCommittedLogLb; exact ApiImpl.committed_confDecodes_impl γ N l

/-- **A committed empty `ConfChangeV2` is at a joint configuration** (2026-10-29, stage U5): raft's
automatic leave, or a client's explicit empty change, is appended only at a joint configuration with
every conf entry before it applied (`stepLeader`'s `alreadyJoint && !wantsLeaveJoint` refusal), so
applying it (leaving the joint configuration) is defined. -/
theorem committed_emptyV2_joint (γ : Cluster) (N : Namespace) (l : List LogEntry) (k : Nat)
    (e : LogEntry) (m : Membership) :
    l[k]? = some e → e.isEmptyV2 →
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ⊢ ⌜m.isJoint⌝ := by
  intro hk he
  unfold isCluster isCommittedLogLb confAt
  exact ApiImpl.committed_emptyV2_joint_impl γ N l k e m hk he

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

/-- **Every conf entry of `l` in `[a, b)` is decided `.skip`** (persistent; §4 of the decision
switch): what `node.ApplyConfChange` and `node.Advance` take for the conf entries their view passes
(until then none at all, `NoConfChangeIn`). -/
def skippedIn (γ : Cluster) (l : List LogEntry) (a b : Nat) : IProp GF :=
  [∗list] j ∈ List.range' a (b - a),
    iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ → confDecided γ j .skip)

instance skippedIn_persistent (γ : Cluster) (l : List LogEntry) (a b : Nat) :
    Persistent (skippedIn (GF := GF) γ l a b) := by
  unfold skippedIn; infer_instance

/-- With no conf entry in the range, nothing to decide. -/
theorem skippedIn_noConf (γ : Cluster) (l : List LogEntry) (a b : Nat) :
    NoConfChangeIn l a b → ⊢ skippedIn (GF := GF) γ l a b := by
  intro hn
  unfold skippedIn
  have H : ∀ xs : List Nat, (∀ j ∈ xs, a ≤ j ∧ j < b) →
      ⊢ [∗list] j ∈ xs, iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ →
        confDecided (GF := GF) γ j .skip) := by
    intro xs
    induction xs with
    | nil => intro _; iapply BigSepL.bigSepL_nil.2; iempintro
    | cons j xs ih =>
      intro hx
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iintro %e %he
        exfalso
        exact absurd he.2 (hn j e (hx j (List.mem_cons_self ..)).1 (hx j (List.mem_cons_self ..)).2 he.1)
      iapply ih (fun x h => hx x (List.mem_cons_of_mem _ h))
  exact H _ (fun j hj => by have := List.mem_range'_1.1 hj; omega)

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
