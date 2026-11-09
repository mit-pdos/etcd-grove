/-
Lean-first (no Rocq counterpart).

# What a step of the trace specification needs of a state (layer C's `trace.go`, 2026-11-09)

The premises the actions take (layer C's progress paragraphs in `notes/trace-validation-plan.md`),
gathered for the specs of `nonReceive`, `Next` and `StepLine`, which call them on every server of the
trace and on every message of the state: the Go's `int`s far from overflow, the bags as the Go's `Bag`
handles them (`Bag.Ok`), the flags the workload leaves off (`PreVote`, `CheckQuorum`), and a line of a
kind the workload logs (no configuration change, restart or snapshot outside the bootstrap: P1-P3 of
`notes/trace-validation-sim.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-- The bounds and flags the actions `nonReceive` calls need of a state: `PreVote` and `CheckQuorum`
off (`RequestPreVote`, `PreTimeout`, `IgnoreInLease`), the pending bag `Bag.Ok` and the two bags' total
counts below `2^63` (`send`, `Ready`'s `Plus`), the reconfiguration count below `2^63 - 1`
(`ApplySimpleConfChange`), and of every server: its log below `2^62 - 1` (`HasNoConflict`'s `len + 1`,
`AppendEntriesInRangeToPeer`'s range up to `len + 1`), its granted votes and configuration below
`2^62` (`IsQuorum`), its term below `2^63 - 1` (`Timeout`), its progress in `[0, 2^62 - 1)` (the range's
low end). -/
def State.ActOk (st : State) : Prop :=
  st.preVote = false ∧ st.checkQuorum = false ∧ st.pendingMessages.Ok ∧
  (((st.pendingMessages.map Prod.snd).sum + (st.messages.map Prod.snd).sum : Nat) : Int) < 2 ^ 63 ∧
  st.reconfigCount + 1 < 2 ^ 63 ∧
  ∀ i ∈ st.server, (st.s i).log.length + 1 < 2 ^ 62 ∧ (st.s i).votesGranted.length < 2 ^ 62 ∧
    (st.s i).currentTerm < 2 ^ 63 - 1 ∧ (st.getConfig i).length < 2 ^ 62 ∧
    ∀ j, 0 ≤ (st.s i).matchIndex j ∧ (st.s i).matchIndex j + 1 < 2 ^ 62

/-- A line of a kind the workload logs outside its bootstrap: not a configuration change
(`ChangeConf`, P3), a restart (`InitState`, P1) or a snapshot sent (`MsgSnap`, P2); the actions of
those kinds have no spec (`notes/trace-validation-plan.md`, layer C). -/
def Line.InScope (ln : Line) : Prop :=
  ln.ev.name ≠ "ChangeConf" ∧ ln.ev.name ≠ "InitState" ∧
  (ln.ev.name = "SendAppendEntriesRequest" → ln.ev.msg.map EventMsg.type ≠ some "MsgSnap")

/-- `State.Receive`'s premises of every message of the state (`receive`'s): none a pre-vote one or a
snapshot, `prevLogIndex` in `[0, 2^62 - 1)`, entries and the destination's log below `2^62`. -/
def State.MsgsOk (st : State) : Prop :=
  st.messages.Ok ∧
  ∀ m ∈ st.messages.domain, m.type ≠ .preVoteRequest ∧ m.type ≠ .preVoteResponse ∧
    m.subtype ≠ "snapshot" ∧ 0 ≤ m.prevLogIndex ∧ m.prevLogIndex + 1 < 2 ^ 62 ∧
    m.entries.length < 2 ^ 62 ∧ (m.dest ∈ st.server → (st.s m.dest).log.length < 2 ^ 62)

/-- What `Next` needs of a state of the trace specification at a line it reads: a position in the
trace, the trace's servers, the actions' bounds, a line in scope where it is not a bootstrap line. -/
def TState.NextOk (tr : Trace) (ts : TState) : Prop :=
  1 ≤ ts.l ∧ ts.s.server = tr.server ∧ ts.s.ActOk ∧ ts.s.MsgsOk ∧
  (ts.l ≤ tr.len → tr.bootstrap.getD (ts.l - 1) false = false → (tr.line ts.l).InScope)

/-! ## Folds in `EvalM`, a step at a time (the loops of `nonReceive`) -/

theorem foldlM_except_append {α β ε : Type} (f : β → α → Except ε β) (l1 l2 : List α) (b : β) :
    (l1 ++ l2).foldlM f b = (l1.foldlM f b) >>= fun c => l2.foldlM f c := by
  rw [List.foldlM_append]

/-- A fold that evaluates evaluates at each step: the next element's step from the prefix's result. -/
theorem foldlM_ok_step {α β ε : Type} (f : β → α → Except ε β) (l : List α) (b0 : β) (n : Nat) (x : α)
    (acc c : β) (htot : l.foldlM f b0 = .ok c) (hpre : (l.take n).foldlM f b0 = .ok acc)
    (hx : l[n]? = some x) : ∃ a', f acc x = .ok a' ∧ (l.take (n + 1)).foldlM f b0 = .ok a' := by
  have hsplit : l = l.take (n + 1) ++ l.drop (n + 1) := (List.take_append_drop _ _).symm
  have htake : l.take (n + 1) = l.take n ++ [x] := by rw [List.take_add_one, hx]; rfl
  rw [hsplit, foldlM_except_append, htake, foldlM_except_append, hpre] at htot
  simp only [Bind.bind, Except.bind, List.foldlM_cons, List.foldlM_nil] at htot
  cases hfx : f acc x with
  | error e => rw [hfx] at htot; cases htot
  | ok a' =>
    refine ⟨a', rfl, ?_⟩
    rw [htake, foldlM_except_append, hpre]
    simp [Bind.bind, Except.bind, hfx, Pure.pure, Except.pure]

/-- A fold over `ys.flatMap g` is a fold of folds. -/
theorem foldlM_flatMap {α β γ ε : Type} (f : β → γ → Except ε β) (g : α → List γ) :
    ∀ (ys : List α) (b : β), (ys.flatMap g).foldlM f b = ys.foldlM (fun acc y => (g y).foldlM f acc) b
  | [], b => rfl
  | y :: ys, b => by
    rw [List.flatMap_cons, foldlM_except_append, List.foldlM_cons]
    simp only [Bind.bind]
    congr 1
    funext c
    exact foldlM_flatMap f g ys c

/-- A fold over the trace's pairs of servers is a fold over its servers of folds over its servers. -/
theorem Trace.pairs_foldlM {β ε : Type} (t : Trace) (f : β → ID × ID → Except ε β) (b : β) :
    t.pairs.foldlM f b = t.server.foldlM (fun acc i => t.server.foldlM (fun acc j => f acc (i, j)) acc) b := by
  unfold Trace.pairs
  rw [foldlM_flatMap]
  congr 1
  funext acc i
  rw [List.foldlM_map]

/-- `flatMap` over the trace's pairs, server by server. -/
theorem Trace.pairs_flatMap {β : Type} (t : Trace) (f : ID × ID → List β) :
    t.pairs.flatMap f = t.server.flatMap (fun i => t.server.flatMap (fun j => f (i, j))) := by
  unfold Trace.pairs
  rw [List.flatMap_assoc]
  congr 1
  funext i
  rw [List.flatMap_map]

/-- A `do`-block's evaluation that ends in `pure`: the bound evaluation's. -/
theorem except_bind_pure_ok {α β ε : Type} (x : Except ε α) (k : α → β) (r : β)
    (h : (x >>= fun a => pure (k a)) = .ok r) : ∃ a, x = .ok a ∧ r = k a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, by simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h; exact h.symm⟩

theorem intRange_length (lo hi : Int) : (intRange lo hi).length = (hi - lo + 1).toNat := by
  simp [intRange]

theorem intRange_getElem? (lo hi : Int) (k : Nat) (hk : k < (hi - lo + 1).toNat) :
    (intRange lo hi)[k]? = some (lo + k) := by
  simp [intRange, List.getElem?_map, List.getElem?_range hk]

end Etcdraft
end EtcdGrove
end Perennial
