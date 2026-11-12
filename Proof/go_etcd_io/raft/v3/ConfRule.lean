/-
# The unified node API's configuration vocabulary (2026-10-28, stage U1; the conf-change decision switch)

The pure vocabulary of the unified node API's section 1 (`notes/spec-first-study/
raft-node-unified-candidate.md`) that is about configurations, with its laws proved, over the API's
sealed `Membership.Valid` and `Membership.applyChange` (`InvNode.lean`):

* `Membership.empty`, `Membership.ids`, `Membership.isJoint`, `Membership.WellFormed` (empty or
  valid: what `Restore` accepts);
* `ccDecode`, `ConfEntryDecodes`: a conf entry's change as `proto.Unmarshal` decodes it;
* `ConfDecision` (apply a change, or skip the entry) and its `step`: the client's decisions, which
  raft's cluster records (`InvNodeRule.lean`);
* `ConfRule`: a client's rule for deciding conf entries (apply a change, or skip: `none`), with
  `ConfDecision.ofRule`, what the client library `ConfPolicy.lean` decides by;
* `CSLists.Is`, `SnapRec`: a snapshot's lists against a membership, a snapshot made.

(2026-10-28, the conf-change decision switch, §5: `ConfRule.Ok`, `clamp*`, `validated*`,
`Membership.fold` and its laws, `RaftLeave`, `opsOfRule` left the API with the cluster of a rule
fixed at allocation; a later stage restates what it needs.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ### Memberships -/

/-- The empty membership: a fresh tracker's, and a stopped node's `nil` `ConfState`'s. -/
def Membership.empty : Membership := ⟨∅, ∅, ∅, ∅, false⟩

/-- A joint configuration: it has outgoing voters. -/
def Membership.isJoint (m : Membership) : Prop := m.votersOutgoing ≠ ∅

/-- **A well-formed membership**: `confchange`'s invariants (`Valid`), or the empty membership (a
fresh tracker's, a stopped node's `nil` `ConfState`): what `Restore` accepts. -/
def Membership.WellFormed (m : Membership) : Prop := m = Membership.empty ∨ m.Valid

theorem Membership.WellFormed.of_valid {m : Membership} (h : m.Valid) : m.WellFormed := .inr h

theorem Membership.wellFormed_empty : Membership.empty.WellFormed := .inl rfl

/-! ### Decoding a conf entry -/

/-- **The decoded change of a conf entry** (`EntryConfChange`: a `ConfChange`; `EntryConfChangeV2`:
a `ConfChangeV2`), as `proto.Unmarshal` gives it (`ccDecodeV1`/`ccDecodeV2`); `none` for an entry
of another type or bytes that do not decode. -/
def ccDecode (e : LogEntry) : Option ConfChangeIM :=
  if e.type = W32 1 then (ccDecodeV1 e.data).map .v1
  else if e.type = W32 2 then (ccDecodeV2 e.data).map .v2
  else none

/-- A conf entry's bytes decode. -/
def ConfEntryDecodes (e : LogEntry) : Prop := ∃ o, ccDecode e = some o

/-- Only a conf entry decodes. -/
theorem ccDecode_isConfChange {e : LogEntry} {o : ConfChangeIM} (h : ccDecode e = some o) :
    e.isConfChange := by
  unfold ccDecode at h
  unfold LogEntry.isConfChange
  by_cases h1 : e.type = W32 1
  · exact .inl h1
  · rw [ite_eq_right h1] at h
    by_cases h2 : e.type = W32 2
    · exact .inr h2
    · rw [ite_eq_right h2] at h; cases h

instance (e : LogEntry) : Decidable e.isConfChange := by
  unfold LogEntry.isConfChange; infer_instance

/-! ### A client's rule -/

/-- **A client's rule for a committed conf entry** `e` after the log `pre`, at the membership `m`
that log gives: apply the change `o` (`some o`; etcd's rejection is a change with `NodeID` 0, which
`confchange` skips) or skip the entry without calling `ApplyConfChange` (`none`: the membership is
kept, joint or not). A client's explicit `ConfChangeV2{}` and raft's automatic leave have the same
(empty) bytes; the rule decides both. Raft's API takes decisions, not rules (`confDecide`); the
client library `ConfPolicy.lean` decides by one. -/
def ConfRule := List LogEntry → Membership → LogEntry → Option ConfChangeIM

/-! ### Decisions (candidate 13's vocabulary, 2026-10-28, stage U4a) -/

/-- **A decision on a committed conf entry** (candidate 13, section 13.1): apply the change `o`, or
skip the entry (the application does not call `ApplyConfChange`). -/
inductive ConfDecision where
  | apply (o : ConfChangeIM)
  | skip

/-- The membership after a decision at `m`: an applied change's result (`none` where `confchange`
refuses it), a skip keeps `m`. (Candidate 13 filters the result by `Valid`; a change keeps a valid
membership valid, `Membership.applyChange_valid`, so the filter is the identity at a valid `m`.) -/
def ConfDecision.step : ConfDecision → Membership → Option Membership
  | .apply o, m => Membership.applyChange o m
  | .skip, m => some m

/-- A rule's answer as a decision: its change applied, its `none` a skip. -/
def ConfDecision.ofRule : Option ConfChangeIM → ConfDecision
  | some o => .apply o
  | none => .skip

/-! ### Snapshots -/

/-- The lists of a `ConfState` report the membership `m` (`confStateIs`, on the lists). -/
def CSLists.Is (cl : CSLists) (m : Membership) : Prop :=
  cl.voters ≡ₚ GMap.elements m.voters ∧ cl.outgoing ≡ₚ GMap.elements m.votersOutgoing ∧
    cl.learners ≡ₚ GMap.elements m.learners ∧ cl.learnersNext ≡ₚ GMap.elements m.learnersNext

/-- **A snapshot the application made** (the candidate's `SnapRec`): the length of the committed
prefix it covers, the membership of that prefix, its data. -/
structure SnapRec where
  index : Nat
  conf : Membership
  data : List w8

end pure

end EtcdGrove
end Perennial
