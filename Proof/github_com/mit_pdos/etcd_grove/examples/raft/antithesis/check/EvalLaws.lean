/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): pure laws of the Lean transcription's
evaluation monad (`EvalM`, `andM`, `orM`) and of Go's `==` on `int`s, for the action proofs: a
premise `act … = .ok r` is taken apart with them into the results of its parts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep
public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

theorem bind_ok {α β : Type} {m : EvalM α} {f : α → EvalM β} {r : β} (h : (m >>= f) = .ok r) :
    ∃ x, m = .ok x ∧ f x = .ok r := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok x => rw [hm] at h; exact ⟨x, rfl, h⟩

@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → EvalM β) : ((Except.ok x : EvalM α) >>= f) = f x := rfl

@[simp] theorem error_bind {α β : Type} (e : String) (f : α → EvalM β) :
    ((Except.error e : EvalM α) >>= f) = Except.error e := rfl

@[simp] theorem ok_map {α β : Type} (x : α) (f : α → β) : (f <$> (Except.ok x : EvalM α)) = .ok (f x) := rfl

@[simp] theorem error_map {α β : Type} (e : String) (f : α → β) :
    (f <$> (Except.error e : EvalM α)) = Except.error e := rfl

@[simp] theorem pure_ok {α : Type} (x : α) : (Pure.pure x : EvalM α) = .ok x := rfl

theorem orM_ok {a b : EvalM Bool} {r : Bool} (h : orM a b = .ok r) :
    ∃ x, a = .ok x ∧ (x = true → r = true) ∧ (x = false → b = .ok r) := by
  unfold orM at h
  obtain ⟨x, hx, h⟩ := bind_ok h
  refine ⟨x, hx, fun hx' => ?_, fun hx' => ?_⟩ <;> subst hx' <;> simp at h
  · exact h
  · exact h

theorem andM_ok {a b : EvalM Bool} {r : Bool} (h : andM a b = .ok r) :
    ∃ x, a = .ok x ∧ (x = true → b = .ok r) ∧ (x = false → r = false) := by
  unfold andM at h
  obtain ⟨x, hx, h⟩ := bind_ok h
  refine ⟨x, hx, fun hx' => ?_, fun hx' => ?_⟩ <;> subst hx' <;> simp at h
  · exact h
  · exact h

@[simp] theorem orM_ok_true (b : EvalM Bool) : orM (.ok true) b = .ok true := rfl
@[simp] theorem orM_ok_false (b : EvalM Bool) : orM (.ok false) b = b := by
  unfold orM; cases b <;> rfl
@[simp] theorem andM_ok_true (b : EvalM Bool) : andM (.ok true) b = b := by
  unfold andM; cases b <;> rfl
@[simp] theorem andM_ok_false (b : EvalM Bool) : andM (.ok false) b = .ok false := rfl

theorem fieldEq_ok {α : Type} [BEq α] {x : Option α} {v : α} {r : Bool} (h : fieldEq x v = .ok r) :
    ∃ y, need x = .ok y ∧ r = (y == v) := by
  unfold fieldEq at h
  obtain ⟨y, hy, h⟩ := bind_ok h
  exact ⟨y, hy, by simp at h; exact h.symm⟩

theorem need_some {α : Type} (a : α) : need (some a) = .ok a := rfl

theorem need_ok {α : Type} {x : Option α} {a : α} (h : need x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some b => cases h; rfl

theorem decide_eq_beq' {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    decide (a = b) = (a == b) := by
  by_cases h : a = b <;> simp [h]

theorem not_decide_eq_bne {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    (!decide (a = b)) = (a != b) := by
  by_cases h : a = b <;> simp [h]

theorem beq_of_eq' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) : (a == b) = true := by
  subst h; exact beq_self_eq_true a

theorem beq_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : ¬ a = b) : (a == b) = false := by
  simpa using h

/-- Go's `==` on `int`s is the Lean's `=` on their values. -/
theorem decide_w64_eq (r u : w64) : decide (r = u) = decide (sint.Z r = sint.Z u) := by
  by_cases h : r = u
  · subst h; simp
  · rw [decide_eq_false h, decide_eq_false (fun h' => h (by word))]

/-! ## `ev.has(F)` for each bit the checker tests (`Event.has`'s premise) -/

section hasF
set_option linter.unusedSimpArgs false

theorem Event.hasF_By (ev : Event) : ev.hasF fBy = some ev.byE.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Role (ev : Event) : ev.hasF fRole = some ev.role.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Term (ev : Event) : ev.hasF fTerm = some ev.term.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Vote (ev : Event) : ev.hasF fVote = some ev.vote.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Commit (ev : Event) : ev.hasF fCommit = some ev.commit.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_First (ev : Event) : ev.hasF fFirst = some ev.first.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Entries (ev : Event) : ev.hasF fEntries = some ev.entries.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_LastIndex (ev : Event) : ev.hasF fLastIndex = some ev.lastIndex.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_LastTerm (ev : Event) : ev.hasF fLastTerm = some ev.lastTerm.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Applied (ev : Event) : ev.hasF fApplied = some ev.applied.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Voters (ev : Event) : ev.hasF fVoters = some ev.voters.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Outgoing (ev : Event) : ev.hasF fOutgoing = some ev.outgoing.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Snap (ev : Event) : ev.hasF fSnap = some ev.snap.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Msg (ev : Event) : ev.hasF fMsg = some ev.msg.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Cause (ev : Event) : ev.hasF fCause = some ev.cause.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_B (ev : Event) : ev.hasF fB = some ev.b := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_A (ev : Event) : ev.hasF fA = some ev.a := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_W (ev : Event) : ev.hasF fW = some ev.w.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_More (ev : Event) : ev.hasF fMore = some ev.more.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Index (ev : Event) : ev.hasF fIndex = some ev.index.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

theorem Event.hasF_Ctx (ev : Event) : ev.hasF fCtx = some ev.ctx.isSome := by
  simp [Event.hasF, fBy, fRole, fTerm, fVote, fCommit, fFirst, fEntries, fLastIndex, fLastTerm, fApplied, fVoters, fOutgoing, fSnap, fMsg, fCause, fB, fA, fW, fMore, fIndex, fCtx]

end hasF

/-! ## `int` arithmetic, as lemmas (a `word` inside a long proof can fail the kernel) -/

theorem sint_sub_one {k : w64} (h : 1 ≤ sint.Z k) : sint.Z (k - W64 1) = sint.Z k - 1 := by word
theorem sint_sub_two {k : w64} (h : 2 ≤ sint.Z k) : sint.Z (k - W64 2) = sint.Z k - 2 := by word
theorem sint_add_one {k : w64} (h : sint.Z k < 2 ^ 63 - 1) : sint.Z (k + W64 1) = sint.Z k + 1 := by word
theorem sint_nat_cast {k : w64} (h : 0 ≤ sint.Z k) : (sint.nat k : Int) = sint.Z k := by word
theorem sint_nat_cast' (k : w64) : (sint.nat k : Int) = max (sint.Z k) 0 := by word
theorem sint_lt_bound (k : w64) : sint.Z k < 2 ^ 63 := by word
theorem sint_ge_bound (k : w64) : -2 ^ 63 ≤ sint.Z k := by word
/-- A loop index below a slice's length: one more is an `int`. -/
theorem sint_add_one_lt {k l : w64} (h : sint.Z k < sint.Z l) : sint.Z (k + W64 1) = sint.Z k + 1 :=
  sint_add_one (by have := sint_lt_bound l; omega)
theorem sint_add {a b : w64} (h1 : -2 ^ 63 ≤ sint.Z a + sint.Z b) (h2 : sint.Z a + sint.Z b < 2 ^ 63) :
    sint.Z (a + b) = sint.Z a + sint.Z b := by word
theorem sint_sub {a b : w64} (h1 : -2 ^ 63 ≤ sint.Z a - sint.Z b) (h2 : sint.Z a - sint.Z b < 2 ^ 63) :
    sint.Z (a - b) = sint.Z a - sint.Z b := by word
theorem sint_one : sint.Z (W64 1) = 1 := rfl
theorem sint_zero : sint.Z (W64 0) = 0 := rfl

theorem range_drop_cons (m j : Nat) (h : j < m) : (List.range m).drop j = j :: (List.range m).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]; simp

end AntCheck
end EtcdGrove
end Perennial
