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

/-! ## What `NewTrace` establishes of a trace (`Trace.Valid`) -/

theorem Trace.Valid.len_lt {tr : Trace} (h : tr.Valid) : (tr.len : Int) < numBound := by
  obtain ⟨evs, -, hlt, hnt⟩ := h
  rw [newTraceWith_len evs false false tr hnt]; exact hlt

theorem Trace.Valid.bootstrap_length {tr : Trace} (h : tr.Valid) : tr.bootstrap.length = tr.len := by
  obtain ⟨evs, -, -, hnt⟩ := h
  rw [(newTraceWith_ok evs false false tr hnt).2]
  simp [Trace.len]

/-! ## `StepLine`'s search -/

/-- What `Violated` needs of a state: its servers' logs below `2^63 - 1`, configurations below `2^62`. -/
def State.ViolOk (st : State) : Prop :=
  (∀ i ∈ st.server, ((st.s i).log.length : Int) < 2 ^ 63 - 1) ∧ (∀ i ∈ st.server, (st.getConfig i).length < 2 ^ 62)

/-- The states `StepLine`'s search from `ts` expands: `ts`, and every successor of an expanded state that
stays at its line (a received message's intermediate steps). -/
inductive Trace.LineReach (tr : Trace) (ts : TState) : TState → Prop
  | start : Trace.LineReach tr ts ts
  | step (f : TState) (tss : List TState) (s2 : TState) :
      Trace.LineReach tr ts f → tr.next f = .ok tss → s2 ∈ tss → s2.l ≠ ts.l + 1 → Trace.LineReach tr ts s2

/-- What `StepLine` needs of its search from `ts` (its spec's premise): every state it expands meets
`Next`'s premises, and, with the invariants checked, every state it reaches meets `Violated`'s. -/
def Trace.StepLineOk (tr : Trace) (ts : TState) (invariants : Bool) : Prop :=
  (∀ f, tr.LineReach ts f → f.NextOk tr) ∧
  (invariants = true → ∀ f tss s2, tr.LineReach ts f → tr.next f = .ok tss → s2 ∈ tss → s2.s.ViolOk)

theorem memEq_of_findIdx?_some {xs : List TState} {ts : TState} {i : Nat}
    (h : xs.findIdx? (fun us => us.eq ts) = some i) : memEq xs ts = true := by
  unfold memEq
  have : (xs.findIdx? (fun us => us.eq ts)).isSome = true := by rw [h]; rfl
  rw [List.findIdx?_isSome] at this
  exact this

theorem memEq_of_findIdx?_none {xs : List TState} {ts : TState}
    (h : xs.findIdx? (fun us => us.eq ts) = none) : memEq xs ts = false := by
  unfold memEq
  have : (xs.findIdx? (fun us => us.eq ts)).isSome = false := by rw [h]; rfl
  rw [List.findIdx?_isSome] at this
  exact this

theorem invariants_names_ne : ∀ p ∈ invariants, p.1 ≠ "" := by
  intro p hp
  simp only [invariants, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A violation's name is never empty (the Go's `Violated` returns `""` for none). -/
theorem State.violated_some_ne {st : State} {v : String} (h : st.violated = .ok (some v)) : v ≠ "" := by
  unfold State.violated at h
  suffices H : ∀ (l : List (String × (State → EvalM Bool))) (a : Option String),
      (∀ p ∈ l, p.1 ≠ "") → (∀ w, a = some w → w ≠ "") →
      ∀ r, l.foldlM (fun acc inv => do
        match acc with
        | some v => return some v
        | none => return if (← inv.2 st) then none else some inv.1) a = .ok r → ∀ w, r = some w → w ≠ "" from
    H invariants none invariants_names_ne (by simp) _ h v rfl
  intro l
  induction l with
  | nil => intro a _ ha r hr; simp [Pure.pure, Except.pure] at hr; subst hr; exact ha
  | cons p l ih =>
    intro a hl ha r hr
    rw [List.foldlM_cons] at hr
    simp only [Bind.bind, Except.bind] at hr
    split at hr
    · cases hr
    · rename_i b hb
      refine ih b (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_ r hr
      intro w hw
      cases a with
      | some v0 => simp [Pure.pure, Except.pure] at hb; subst hb; cases hw; exact ha _ rfl
      | none =>
        simp only at hb
        cases hp : p.2 st with
        | error e => rw [hp] at hb; cases hb
        | ok c =>
          rw [hp] at hb
          simp [Pure.pure, Except.pure] at hb
          subst hb
          cases c with
          | true => simp at hw
          | false => simp at hw; subst hw; exact hl p List.mem_cons_self

/-- `stepRound`'s step on one successor (its inner fold's function). -/
def Trace.stepInnerF (l0 : Nat) (invariants : Bool)
    (acc : List TState × List TState × List TState × List TState × StepInfo) (s2 : TState) :
    EvalM (List TState × List TState × List TState × List TState × StepInfo) := do
  let (out, visited, next, fresh, info) := acc
  if info.violation.isSome then return acc
  let (out, visited, next, isNew) :=
    if s2.l == l0 + 1 then
      if memEq out s2 then (out, visited, next, false) else (out ++ [s2], visited, next, true)
    else if memEq visited s2 then (out, visited, next, false)
    else (out, visited ++ [s2], next ++ [s2], true)
  if !isNew then return (out, visited, next, fresh, info)
  let fresh := if memEq fresh s2 then fresh else fresh ++ [s2]
  let info ← if invariants then do
      match ← s2.s.violated with
      | some v => pure { info with violation := some v }
      | none => pure info
    else pure info
  return (out, visited, next, fresh, info)

/-- `stepRound`'s step on one state of the frontier (its outer fold's function). -/
def Trace.stepOuterF (t : Trace) (l0 : Nat) (invariants : Bool)
    (acc : List TState × List TState × List TState × StepInfo) (f : TState) :
    EvalM (List TState × List TState × List TState × StepInfo) := do
  let (out, visited, next, info) := acc
  if info.violation.isSome then return acc
  let succ ← t.next f
  let (out, visited, next, fresh, info) ← succ.foldlM (Trace.stepInnerF l0 invariants)
    (out, visited, next, [], info)
  return (out, visited, next,
    if info.violation.isNone && fresh.length > 1 then { info with branched := true } else info)

theorem Trace.stepRound_eq (t : Trace) (l0 : Nat) (invariants : Bool) (frontier : List TState)
    (st : List TState × List TState × StepInfo) :
    t.stepRound l0 invariants frontier st = frontier.foldlM (t.stepOuterF l0 invariants) (st.1, st.2.1, [], st.2.2) :=
  rfl

/-- Past a violation, the inner fold leaves its accumulator. -/
theorem Trace.stepInnerF_foldlM_skip (l0 : Nat) (invariants : Bool) :
    ∀ (l : List TState) (acc : List TState × List TState × List TState × List TState × StepInfo),
      acc.2.2.2.2.violation.isSome = true → l.foldlM (Trace.stepInnerF l0 invariants) acc = .ok acc
  | [], acc, _ => rfl
  | s2 :: l, acc, h => by
    rw [List.foldlM_cons]
    have : Trace.stepInnerF l0 invariants acc s2 = .ok acc := by
      obtain ⟨o, v, n, f, i⟩ := acc
      simp only at h
      simp [Trace.stepInnerF, h, Pure.pure, Except.pure]
    rw [this]
    exact Trace.stepInnerF_foldlM_skip l0 invariants l acc h

/-- Past a violation, the outer fold leaves its accumulator. -/
theorem Trace.stepOuterF_foldlM_skip (t : Trace) (l0 : Nat) (invariants : Bool) :
    ∀ (l : List TState) (acc : List TState × List TState × List TState × StepInfo),
      acc.2.2.2.violation.isSome = true → l.foldlM (t.stepOuterF l0 invariants) acc = .ok acc
  | [], acc, _ => rfl
  | f :: l, acc, h => by
    rw [List.foldlM_cons]
    have : t.stepOuterF l0 invariants acc f = .ok acc := by
      obtain ⟨o, v, n, i⟩ := acc
      simp only at h
      simp [Trace.stepOuterF, h, Pure.pure, Except.pure]
    rw [this]
    exact Trace.stepOuterF_foldlM_skip t l0 invariants l acc h

/-- A frontier state's step, without a violation so far: its successors' fold. -/
theorem Trace.stepOuterF_ok (t : Trace) (l0 : Nat) (invariants : Bool) (o v n : List TState) (i : StepInfo)
    (f : TState) (a' : List TState × List TState × List TState × StepInfo) (hi : i.violation = none)
    (h : t.stepOuterF l0 invariants (o, v, n, i) f = .ok a') :
    ∃ succ, t.next f = .ok succ ∧ ∃ r : List TState × List TState × List TState × List TState × StepInfo,
      succ.foldlM (Trace.stepInnerF l0 invariants) (o, v, n, [], i) = .ok r ∧
      a' = (r.1, r.2.1, r.2.2.1,
        if r.2.2.2.2.violation.isNone && r.2.2.2.1.length > 1 then { r.2.2.2.2 with branched := true }
        else r.2.2.2.2) := by
  unfold Trace.stepOuterF at h
  simp only [hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
  cases hn : t.next f with
  | error e => rw [hn] at h; cases h
  | ok succ =>
    rw [hn] at h
    refine ⟨succ, rfl, ?_⟩
    simp only [Bind.bind, Except.bind] at h
    cases hf : succ.foldlM (Trace.stepInnerF l0 invariants) (o, v, n, [], i) with
    | error e => rw [hf] at h; cases h
    | ok r =>
      rw [hf] at h
      obtain ⟨r1, r2, r3, r4, r5⟩ := r
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      exact ⟨_, rfl, h.symm⟩

/-- The step information after a new state `s2` (its invariants checked when asked). -/
def Trace.stepNewInfo (invariants : Bool) (s2 : TState) (i : StepInfo) : EvalM StepInfo :=
  if invariants then do
    match ← s2.s.violated with
    | some v => pure { i with violation := some v }
    | none => pure i
  else pure i

theorem Trace.stepNewInfo_false (s2 : TState) (i : StepInfo) : Trace.stepNewInfo false s2 i = .ok i := rfl

theorem Trace.stepNewInfo_true (s2 : TState) (i : StepInfo) (r : Option String) (h : s2.s.violated = .ok r) :
    Trace.stepNewInfo true s2 i = .ok (match r with | some v => { i with violation := some v } | none => i) := by
  unfold Trace.stepNewInfo
  simp only [↓reduceIte, h, Bind.bind, Except.bind]
  cases r <;> rfl

theorem Trace.stepInnerF_dup_out (l0 : Nat) (invariants : Bool) (o v n fr : List TState) (i : StepInfo)
    (s2 : TState) (hi : i.violation = none) (hl : s2.l = l0 + 1) (hm : memEq o s2 = true) :
    Trace.stepInnerF l0 invariants (o, v, n, fr, i) s2 = .ok (o, v, n, fr, i) := by
  simp [Trace.stepInnerF, hi, hl, hm, Pure.pure, Except.pure]

theorem Trace.stepInnerF_dup_vis (l0 : Nat) (invariants : Bool) (o v n fr : List TState) (i : StepInfo)
    (s2 : TState) (hi : i.violation = none) (hl : s2.l ≠ l0 + 1) (hm : memEq v s2 = true) :
    Trace.stepInnerF l0 invariants (o, v, n, fr, i) s2 = .ok (o, v, n, fr, i) := by
  simp [Trace.stepInnerF, hi, hl, hm, Pure.pure, Except.pure]

theorem Trace.stepInnerF_new_out (l0 : Nat) (invariants : Bool) (o v n fr : List TState) (i : StepInfo)
    (s2 : TState) (hi : i.violation = none) (hl : s2.l = l0 + 1) (hm : memEq o s2 = false) :
    Trace.stepInnerF l0 invariants (o, v, n, fr, i) s2 =
      (Trace.stepNewInfo invariants s2 i >>= fun i' =>
        pure (o ++ [s2], v, n, (if memEq fr s2 then fr else fr ++ [s2]), i')) := by
  cases invariants
  · simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm]
  · cases hv : s2.s.violated with
    | error e => simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm, hv, Bind.bind, Except.bind]
    | ok r =>
      cases r <;> simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm, hv, Bind.bind, Except.bind, Pure.pure,
        Except.pure]

theorem Trace.stepInnerF_new_vis (l0 : Nat) (invariants : Bool) (o v n fr : List TState) (i : StepInfo)
    (s2 : TState) (hi : i.violation = none) (hl : s2.l ≠ l0 + 1) (hm : memEq v s2 = false) :
    Trace.stepInnerF l0 invariants (o, v, n, fr, i) s2 =
      (Trace.stepNewInfo invariants s2 i >>= fun i' =>
        pure (o, v ++ [s2], n ++ [s2], (if memEq fr s2 then fr else fr ++ [s2]), i')) := by
  cases invariants
  · simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm]
  · cases hv : s2.s.violated with
    | error e => simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm, hv, Bind.bind, Except.bind]
    | ok r =>
      cases r <;> simp [Trace.stepInnerF, Trace.stepNewInfo, hi, hl, hm, hv, Bind.bind, Except.bind, Pure.pure,
        Except.pure]

/-- A fold whose prefix reached a fixed point of the rest's steps ends there. -/
theorem foldlM_take_fix {α β ε : Type} (f : β → α → Except ε β) (l : List α) (b a c : β) (n : Nat)
    (htot : l.foldlM f b = .ok c) (hpre : (l.take n).foldlM f b = .ok a)
    (hfix : ∀ l' : List α, l'.foldlM f a = .ok a) : c = a := by
  rw [← List.take_append_drop n l, foldlM_except_append, hpre] at htot
  simp only [Bind.bind, Except.bind] at htot
  rw [hfix] at htot
  cases htot; rfl

end Etcdraft
end EtcdGrove
end Perennial
