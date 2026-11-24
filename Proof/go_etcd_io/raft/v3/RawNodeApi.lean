/-
Lean-first (#33 S3c step 4, `notes/antithesis-rawnode-design.md` §2.1, §2.6). **The `RawNode` client
API, as statements**: the sealed node predicate `rawNode γ rn id rs ps qs ip` (a `RawNode` in the
Antithesis harness's scope, at the client's record `rs`, its protocol state `ps` and the protocol
messages `qs` queued for `Advance`), the specs of the functions the harness calls over it
(`RawNode.<F>.apiSpec`: `RawNodeAbsSpecs.lean`'s forms at `rawNode`; `ip` its in-progress boundary), the laws a client reads out
of it, and the term budget under sealed names. Every law is a `.law : Prop`, proved with the
strengthened specs (`RawNodeApiLinked.lean`, phase 2); nothing here is assumed.

Not yet in `etc/api/raft.txt` (a later step, with the proofs). When it is listed: the forms'
vocabulary (the message predicates, `ownRawNodeIdle`'s module) is still internal, so this module's
public imports need the API check's review then.

Deviations from the design's §2.1 table (the design's §2.6 lists them): `rawNode_wf` without the
`ps.base = base0 →` guard (`rawNode_noSnap` gives it); `rawNode_outbox` not stated (the outbox's
messages reach the client only through `Ready`'s post, whose *enter* and `Hlead` give each one's
`isRaftMsg`; between inputs the outbox is empty, `PIdle`); `rawNode_commitInv` added (`commitIn_camp`
takes `raftCommitInv`); `rawNode_commit`'s `isCommitted` half a law of its own under an update
(`rawNode_committed`: it is read through the commit invariant); `rawNode_scope` states the mode only
(pre-vote and check-quorum are not in `ps`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import Proof.go_etcd_io.raft.v3.InvNodeChan

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A `RawNode` in the harness's scope** (design §2.1): closed in the cluster `γ`, at the client's
record `rs`, the protocol state `ps` (`PState`, the protocol's own record), the protocol messages
`qs` queued for `Advance` (a leader's self-acknowledgement, a candidate's self-vote) and the
in-progress boundary `ip` (the log's entries the `Ready`s have handed out); static mode,
pre-vote and check-quorum off, never compacted. Sealed. -/
@[no_expose] def rawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState)
    (qs : List Msg) (ip : Nat) : IProp GF :=
  ownRawNodeAt γ rn id rs ps qs ip true

/-! ### The specs, over `rawNode` -/

abbrev RawNode.Step.apiSpec : Prop := RawNode.Step.form (rawNode (GF := GF)) True
abbrev RawNode.Tick.apiSpec : Prop := RawNode.Tick.form (rawNode (GF := GF)) True
abbrev RawNode.Propose.apiSpec : Prop := RawNode.Propose.form (rawNode (GF := GF)) True
abbrev RawNode.Ready.apiSpec : Prop := RawNode.Ready.form (rawNode (GF := GF)) True
abbrev RawNode.Advance.apiSpec : Prop := RawNode.Advance.form (rawNode (GF := GF)) True

/-- `rn.HasReady()`, read-only; on `false` the protocol-level idle fact `PIdle`, the in-progress
boundary at the log's end. -/
abbrev RawNode.HasReady.apiSpec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ rawNode γ rn id rs ps qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      rawNode γ rn id rs ps qs ip ∗ ⌜b = false → PIdle rs ps ∧ ip = ps.log.length⌝ }}

/-- `NewRawNode` at an empty storage: the node at `pInit`, nothing queued. -/
abbrev NewRawNode.emptyStartApiSpec : Prop := NewRawNode.emptyStartForm (rawNode (GF := GF))

/-! ### The laws (design §2.1's table) -/

/-- The log well formed from `base0`, the commit index within it, the term the client's. -/
abbrev rawNode_wf.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ⌜PlogWf base0 ps.log ∧ uint.Z ps.commit ≤ plogLastIndexZ base0 ps.log ∧ ps.term = rs.term⌝ ∗
    rawNode γ rn id rs ps qs ip

/-- No snapshot: the log's boundary `base0`, none lent, no `MsgSnap` queued (§2.5). -/
abbrev rawNode_noSnap.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ⌜ps.base = base0 ∧ rs.slent = none ∧ ∀ m ∈ ps.outbox, m.ty ≠ .snap⌝ ∗
    rawNode γ rn id rs ps qs ip

/-- (#33 S4, drain) The log's terms at most the node's term (raft's ghost `TermsLe`). -/
abbrev rawNode_logTerms.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ⌜∀ e ∈ ps.log, uint.Z e.Term' ≤ uint.Z ps.term⌝ ∗ rawNode γ rn id rs ps qs ip

/-- The static mode (the scope's part a client sees). -/
abbrev rawNode_scope.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗ ⌜rs.mode = .static⌝ ∗ rawNode γ rn id rs ps qs ip

/-- The log's records (`ownLogGhost`'s `Hrecs`): each entry created by its term's leader. -/
abbrev rawNode_logRecs.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗ logRecs γ base0 ps.log ∗ rawNode γ rn id rs ps qs ip

/-- A leader's witness (`leaderWit`) and its campaign log, a prefix of its log (`leadLogOwn`). -/
abbrev rawNode_leader.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    □ (⌜ps.role = .leader⌝ -∗
      isLeader γ id ps.term ∗ ∃ F0 : List EntryM, isCamp γ id ps.term F0 ∗ ⌜F0 <+: ps.log⌝) ∗
    rawNode γ rn id rs ps qs ip

/-- The vote of the client's durable state `S` at its term (`VoteHistOkD`, the vote table). Of the
durable state, not of `rawNode`'s protocol state: a vote a `Step` grants is a promise in the node's
virtual maps, and its `isVote` is minted only when a `Ready`'s *enter* persists it
(`Protocol/Enter.lean`, `votesTbl_insert`); the harness reads it after `Ready`'s `Henter`. Under an
update: the entered votes' fragments are the slot invariant's (`slotBody`'s `durFrags`), read against
the durable half's authority share. -/
abbrev rawNode_vote.law : Prop :=
  ∀ (γ : RaftNames) (id : w64) (S : RaftState),
  ⊢ ownDurGhost (GF := GF) γ id S ={↑(raftN γ)}=∗
    □ (⌜S.vote ≠ W64 0⌝ -∗ isVote γ id S.term S.vote) ∗ ownDurGhost γ id S

/-- The tally's grants, each a vote for the node at its term (`Htally`). -/
abbrev rawNode_tally.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ([∗map] v ↦ _u ∈ toMap (granted ps.votes), isVote γ v ps.term id) ∗ rawNode γ rn id rs ps qs ip

/-- The commit index's witness as known in the node's term (`ownLogGhost`'s `Hcommit`). -/
abbrev rawNode_commit.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    commitIn γ ps.log ps.commit ps.term ∗ rawNode γ rn id rs ps qs ip

/-- The log up to the commit index is committed (`isCommitted`): through the commit invariant
(`commitIn`'s quorum `cq` is within the committed log, `committedJust`, and agrees with the log by
the records), so under an update at raft's namespace. -/
abbrev rawNode_committed.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip ={↑(raftN γ)}=∗
    isCommitted γ (ps.log.take (uint.nat ps.commit)) ∗ rawNode γ rn id rs ps qs ip

/-- The cluster's commit invariant (what `commitIn_camp` opens). -/
abbrev rawNode_commitInv.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗ raftCommitInv γ ∗ rawNode γ rn id rs ps qs ip

/-- (review S6) Every entry of the log is a filler or a proposal a client deposited (`entData`:
its key `deposited`, its bytes decoding as its type says). -/
abbrev rawNode_entries.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ([∗list] e ∈ ps.log, entData γ e) ∗ rawNode γ rn id rs ps qs ip

/-- The term within the ceiling (`ownRawNode_term_tc`). -/
abbrev rawNode_term_tc.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat),
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗
    ⌜uint.Z ps.term ≤ uint.Z rs.tc⌝ ∗ rawNode γ rn id rs ps qs ip

/-- The ceiling raised (`ownRawNode_raise_tc`): a ghost step, the protocol state unchanged. -/
abbrev rawNode_raise_tc.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat) (tc : w64),
  uint.Z rs.tc ≤ uint.Z tc →
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗ rawNode γ rn id { rs with tc := tc } ps qs ip

/-- The storage handshake (`ownRawNode_appended`): the receipt of the client's append of the entries
the last `Ready` handed out (`rs.unpersisted`; `appendReceipt`, for the node's storage) is absorbed;
afterwards nothing is unpersisted. A ghost step: the protocol state, the queue and the in-progress
boundary unchanged. `a`, the batch's frozen prefix, within the committed log handed out. -/
abbrev rawNode_appended.law : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState) (qs : List Msg) (ip : Nat)
    (a : List EntryM), rs.slent = none →
  (a ≠ [] → ∀ e0, rs.unpersisted.head? = some e0 →
     uint.nat e0.Index' - 1 + a.length ≤ rs.delivered.length) →
  ⊢ rawNode (GF := GF) γ rn id rs ps qs ip -∗ appendReceipt rs.storage rs.unpersisted a ==∗
    rawNode γ rn id { rs with unpersisted := [] } ps qs ip

/-! ### The term budget, sealed (decision 2; `InvNodeChan.lean`'s) -/

/-- The cluster's term budget (`budgetInv` in its invariant). Sealed; persistent. -/
@[no_expose] def rnBudget (γ : Cluster) : IProp GF := inv budgetN (budgetInv γ.budget)

/-- The budget's bound is at least `t` (`termLB`). Sealed; persistent. -/
@[no_expose] def rnTermLB (γ : Cluster) (t : w64) : IProp GF := termLB γ.budget t

abbrev rnBudget_persistent.law : Prop := ∀ γ : Cluster, Persistent (rnBudget (GF := GF) γ)

abbrev rnTermLB_persistent.law : Prop :=
  ∀ (γ : Cluster) (t : w64), Persistent (rnTermLB (GF := GF) γ t)

/-- The client's durable state, opened over the sealed names (`raftState_open`). -/
abbrev raftState_open_rn.law : Prop :=
  ∀ (γ : Cluster) (id : w64) (S : RaftState),
    raftState (GF := GF) γ id S ⊣⊢ ownDurGhost γ.raftNames id S ∗ rnTermLB γ S.term ∗ rnBudget γ

/-- A time receipt buys one more term (`budget_spend`; `tickCred bud 1` is `⧗ 1`). -/
abbrev rnBudget_spend.law : Prop :=
  ∀ (γ : Cluster) (t : w64) (E : CoPset), ↑budgetN ⊆ E →
  ⊢ rnBudget (GF := GF) γ -∗ ⧗ 1 -∗ rnTermLB γ t ={E}=∗
    ⌜uint.Z t + 1 < 2 ^ 64 - 1⌝ ∗ rnTermLB γ (t + W64 1)

/-- Two bounds (a node's and a message's term) give one above both, past one more for a receipt
(`budget_step`). -/
abbrev rnBudget_step.law : Prop :=
  ∀ (γ : Cluster) (t1 t2 : w64) (P : Prop) [Decidable P] (E : CoPset), ↑budgetN ⊆ E →
  ⊢ rnBudget (GF := GF) γ -∗ rnTermLB γ t1 -∗ rnTermLB γ t2 -∗ ⧗ (if P then 1 else 0) ={E}=∗
    ⌜uint.Z t1 + 1 < 2 ^ 64 ∧ uint.Z t2 + 1 < 2 ^ 64⌝ ∗
    ∃ tb : w64, rnTermLB γ tb ∗ ⌜max (uint.Z t1) (uint.Z t2) + (if P then 1 else 0) ≤ uint.Z tb⌝

/-- Monotone (`termLB_le`). -/
abbrev rnTermLB_le.law : Prop :=
  ∀ (γ : Cluster) (t t' : w64), uint.Z t' ≤ uint.Z t →
  ⊢ rnTermLB (GF := GF) γ t -∗ rnTermLB γ t'

/-- No term at the last value (`termLB_bound`). -/
abbrev rnTermLB_bound.law : Prop :=
  ∀ (γ : Cluster) (t : w64) (E : CoPset), ↑budgetN ⊆ E →
  ⊢ rnBudget (GF := GF) γ -∗ rnTermLB γ t ={E}=∗ ⌜uint.Z t < 2 ^ 64 - 1⌝

/-- At most the receipts' bound (`termLB_rb`, `TracedNodeRun.lean`). -/
abbrev rnTermLB_rb.law : Prop :=
  ∀ (γ : Cluster) (t : w64) (E : CoPset), ↑budgetN ⊆ E →
  ⊢ rnBudget (GF := GF) γ -∗ rnTermLB γ t ={E}=∗ ⌜uint.nat t ≤ receiptBound GF⌝

end api

end EtcdGrove
end Perennial
