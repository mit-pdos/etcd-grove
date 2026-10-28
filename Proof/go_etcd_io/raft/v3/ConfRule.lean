/-
# The unified node API's configuration vocabulary (2026-10-28, stage U1)

The pure vocabulary of the unified node API's section 1 (`notes/spec-first-study/
raft-node-unified-candidate.md`) that is about configurations, with its laws proved, over the API's
sealed `Membership.Valid` and `Membership.applyChange` (`InvNode.lean`):

* `Membership.empty`, `Membership.ids`, `Membership.isJoint`, `Membership.WellFormed` (empty or
  valid: what `Restore` accepts);
* `ccDecode`, `ConfEntryDecodes`: a conf entry's change as `proto.Unmarshal` decodes it;
* `ConfRule`: the application's decision on each committed conf entry (apply a change, or reject the
  entry: `none`), `ConfRule.Ok` (it applies only changes with a valid result), `ConfRule.clamp`
  (any rule made `Ok`, pointwise), `ConfRule.validated` (raft's own validation: the decoded change
  where its result is valid);
* `Membership.fold r c0 l`: the membership after the log `l`, from `c0`, its conf entries decided by
  `r` (`fold_total`, `fold_nil`, `fold_snoc_normal`, `fold_snoc_conf`);
* `RaftLeave`: raft's automatic leave of a joint configuration (an empty `EntryConfChangeV2` where
  the configuration is joint and left automatically); `opsOfRule r c0 l`: the requested entries
  (fillers and raft's leaves dropped; `opsOfRule_noType2`).

Nothing here is used by the node specs yet (stages U6, U9): `opsOfRule` is the candidate's
`opsOf r c0`, beside today's `opsOf` (`NodeApiVocab.lean`), which `ownCommittedOps` still means
until U9. The bridge to the protocol's decoder (`ConfRule.toDec`) is in `ConfRuleDec.lean`
(internal).
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

/-- Every id a membership tracks. -/
def Membership.ids (m : Membership) : GSet w64 :=
  m.voters ∪ m.votersOutgoing ∪ m.learners ∪ m.learnersNext

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

/-! ### The application's rule -/

/-- **The application's decision on a committed conf entry** `e` after the log `pre`, at the
membership `m` that log gives: apply the change `o` (`some o`; etcd's rejection is a change with
`NodeID` 0, which `confchange` skips) or reject the entry without calling `ApplyConfChange`
(`none`: the membership is kept, joint or not). A client's explicit `ConfChangeV2{}` and raft's
automatic leave have the same (empty) bytes; the rule decides both. -/
def ConfRule := List LogEntry → Membership → LogEntry → Option ConfChangeIM

/-- **A rule applies only changes whose result is valid** (`confchange` accepts it, and it stays
within raft's bound on the tracked ids: `ccStepB`), at a valid membership. -/
def ConfRule.Ok (r : ConfRule) : Prop :=
  ∀ pre m e o, m.Valid → r pre m e = some o →
    ∃ m', Membership.applyChange o m = some m' ∧ m'.Valid

open Classical in
/-- **A rule made `Ok`**: its changes whose result is not valid rejected. -/
def ConfRule.clamp (r : ConfRule) : ConfRule := fun pre m e =>
  (r pre m e).filter fun o => decide (∃ m', Membership.applyChange o m = some m' ∧ m'.Valid)

open Classical in
theorem ConfRule.clamp_ok (r : ConfRule) : (ConfRule.clamp r).Ok := by
  intro pre m e o _ h
  unfold ConfRule.clamp at h
  cases h1 : r pre m e with
  | none => rw [h1] at h; cases h
  | some o' =>
    rw [h1, Option.filter_some] at h
    split at h
    · rename_i hp; cases h; exact of_decide_eq_true hp
    · cases h

open Classical in
/-- Clamping an `Ok` rule changes nothing at a valid membership. -/
theorem ConfRule.clamp_eq (r : ConfRule) (pre : List LogEntry) (m : Membership) (e : LogEntry)
    (hr : r.Ok) (hm : m.Valid) : ConfRule.clamp r pre m e = r pre m e := by
  unfold ConfRule.clamp
  cases h1 : r pre m e with
  | none => rfl
  | some o =>
    rw [Option.filter_some, ite_eq_left (decide_eq_true (hr pre m e o hm h1))]

/-- **Raft's validation as the rule** (kvreconf's `validConf`): the entry's decoded change, applied
where its result is valid; rejected otherwise (an entry that does not decode included). -/
def ConfRule.validated : ConfRule := ConfRule.clamp fun _ _ e => ccDecode e

theorem ConfRule.validated_ok : ConfRule.validated.Ok := ConfRule.clamp_ok _

/-! ### The membership of a log -/

/-- One entry after the log `pre`, at the membership `m`: a conf entry decided by `r` (a rejection
keeps `m`, a change is applied); any other entry keeps `m`. -/
def Membership.foldStep (r : ConfRule) (pre : List LogEntry) (m : Membership) (e : LogEntry) :
    Option Membership :=
  if e.isConfChange then
    match r pre m e with
    | none => some m
    | some o => Membership.applyChange o m
  else some m

/-- The membership after the entries `l`, from `m`, the log `pre` before them. -/
def Membership.foldFrom (r : ConfRule) (pre : List LogEntry) (m : Membership) :
    List LogEntry → Option Membership
  | [] => some m
  | e :: es => (Membership.foldStep r pre m e).bind fun m' => Membership.foldFrom r (pre ++ [e]) m' es

/-- **The membership after the log `l`**, from `c0`, every conf entry decided by `r` at the
membership the log before it gives; `none` where a change applied fails (never for an `Ok` rule
from a valid `c0`: `fold_total`). -/
def Membership.fold (r : ConfRule) (c0 : Membership) (l : List LogEntry) : Option Membership :=
  Membership.foldFrom r [] c0 l

theorem Membership.foldFrom_append (r : ConfRule) (pre : List LogEntry) (m : Membership)
    (l1 l2 : List LogEntry) :
    Membership.foldFrom r pre m (l1 ++ l2)
      = (Membership.foldFrom r pre m l1).bind fun m' => Membership.foldFrom r (pre ++ l1) m' l2 := by
  induction l1 generalizing m pre with
  | nil => simp [Membership.foldFrom]
  | cons e l ih =>
    simp only [List.cons_append, Membership.foldFrom]
    cases Membership.foldStep r pre m e with
    | none => rfl
    | some m' => simp [ih]

theorem Membership.fold_snoc (r : ConfRule) (c0 : Membership) (l : List LogEntry) (e : LogEntry) :
    Membership.fold r c0 (l ++ [e])
      = (Membership.fold r c0 l).bind fun m => Membership.foldStep r l m e := by
  unfold Membership.fold
  rw [Membership.foldFrom_append, List.nil_append]
  cases Membership.foldFrom r [] c0 l with
  | none => rfl
  | some m =>
    simp only [Option.bind_some, Membership.foldFrom]
    cases Membership.foldStep r l m e <;> rfl

theorem Membership.fold_nil (r : ConfRule) (c0 : Membership) : Membership.fold r c0 [] = some c0 :=
  rfl

/-- An entry that is no conf change keeps the membership. -/
theorem Membership.fold_snoc_normal (r : ConfRule) (c0 : Membership) (l : List LogEntry)
    (e : LogEntry) (h : ¬ e.isConfChange) :
    Membership.fold r c0 (l ++ [e]) = Membership.fold r c0 l := by
  rw [Membership.fold_snoc]
  cases Membership.fold r c0 l with
  | none => rfl
  | some m => simp only [Option.bind_some, Membership.foldStep, ite_eq_right h]

/-- A conf entry: the rule's rejection keeps the membership, its change is applied. -/
theorem Membership.fold_snoc_conf (r : ConfRule) (c0 m : Membership) (l : List LogEntry)
    (e : LogEntry) (h : e.isConfChange) (hm : Membership.fold r c0 l = some m) :
    Membership.fold r c0 (l ++ [e]) = match r l m e with
      | none => some m
      | some o => Membership.applyChange o m := by
  rw [Membership.fold_snoc, hm, Option.bind_some, Membership.foldStep, ite_eq_left h]

/-- **Total for an `Ok` rule from a valid `c0`**: the rule's `none` is a rejection, which keeps the
membership, and its `some o` an accepted change (`Ok`). -/
theorem Membership.fold_total (r : ConfRule) (c0 : Membership) (l : List LogEntry) (hr : r.Ok)
    (h0 : c0.Valid) : ∃ m, Membership.fold r c0 l = some m ∧ m.Valid := by
  suffices H : ∀ (pre : List LogEntry) (m : Membership), m.Valid →
      ∃ m', Membership.foldFrom r pre m l = some m' ∧ m'.Valid from H [] c0 h0
  induction l with
  | nil => intro pre m hm; exact ⟨m, rfl, hm⟩
  | cons e l ih =>
    intro pre m hm
    have hs : ∃ m1, Membership.foldStep r pre m e = some m1 ∧ m1.Valid := by
      unfold Membership.foldStep
      split
      · split
        · exact ⟨m, rfl, hm⟩
        · rename_i o ho; exact hr pre m e o hm ho
      · exact ⟨m, rfl, hm⟩
    obtain ⟨m1, h1, hv1⟩ := hs
    simp only [Membership.foldFrom, h1, Option.bind_some]
    exact ih (pre ++ [e]) m1 hv1

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

/-! ### Raft's automatic leave, and the requested entries -/

/-- **Raft's automatic leave** at the end of the log `pre`: an `EntryConfChangeV2` with empty data
where the membership `pre` gives is joint and left automatically (`raft.appliedTo`'s proposal). -/
def RaftLeave (r : ConfRule) (c0 : Membership) (pre : List LogEntry) (e : LogEntry) : Prop :=
  e.type = W32 2 ∧ e.data = [] ∧
    ∃ m, Membership.fold r c0 pre = some m ∧ m.isJoint ∧ m.autoLeave = true

open Classical in
/-- The requested entries of the entries `l` after the log `pre`: fillers and raft's leaves
dropped. -/
def opsOfRuleFrom (r : ConfRule) (c0 : Membership) (pre : List LogEntry) :
    List LogEntry → List LogEntry
  | [] => []
  | e :: es => (if e.isFiller ∨ RaftLeave r c0 pre e then [] else [e]) ++
      opsOfRuleFrom r c0 (pre ++ [e]) es

/-- **The requested entries of a log** (the candidate's `opsOf r c0`; named apart from today's
`opsOf` until stage U9): everything but its fillers and raft's automatic leaves. -/
def opsOfRule (r : ConfRule) (c0 : Membership) (l : List LogEntry) : List LogEntry :=
  opsOfRuleFrom r c0 [] l

/-- Without an `EntryConfChangeV2` there is no automatic leave: the requested entries are the
non-fillers. -/
theorem opsOfRule_noType2 (r : ConfRule) (c0 : Membership) (l : List LogEntry)
    (h : ∀ e ∈ l, e.type ≠ W32 2) :
    opsOfRule r c0 l = l.filter fun e => !decide e.isFiller := by
  unfold opsOfRule
  suffices H : ∀ pre, opsOfRuleFrom r c0 pre l = l.filter fun e => !decide e.isFiller from H []
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro pre
    have he : ¬ RaftLeave r c0 pre e := fun hl => h e (List.mem_cons_self ..) hl.1
    simp only [opsOfRuleFrom, List.filter_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    by_cases hf : e.isFiller
    · simp [hf]
    · simp [hf, he]

end pure

end EtcdGrove
end Perennial
