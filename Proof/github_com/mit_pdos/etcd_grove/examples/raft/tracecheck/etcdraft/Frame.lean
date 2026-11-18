/-
Lean-first (no Rocq counterpart).

# The trace specification's constants never change (layer C, 2026-11-09)

Every action of `etcdraft` builds its successor from its state with `{ st with … }`, so the
constants `Server`, `PreVote` and `CheckQuorum` are those of `TraceInit` in every state the search
can reach (`Trace.Reach.frame`): the part of `CheckTrace`'s premise about them is proved, not
assumed (`notes/trace-validation-plan.md`, Q10).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StepOk

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-! ## Folds -/

/-- A fold in `Except` keeps an invariant its steps keep. -/
theorem foldlM_except_inv {α β ε : Type} (P : β → Prop) (f : β → α → Except ε β) :
    ∀ (l : List α) (b c : β), (∀ a x c, x ∈ l → P a → f a x = .ok c → P c) → P b →
      l.foldlM f b = .ok c → P c
  | [], b, c, _, hb, h => by
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; exact hb
  | x :: l, b, c, hs, hb, h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hx : f b x with
    | error e => rw [hx] at h; cases h
    | ok b' =>
      rw [hx] at h
      exact foldlM_except_inv P f l b' c (fun a y c hy ha hf => hs a y c (List.mem_cons_of_mem _ hy) ha hf)
        (hs b x b' List.mem_cons_self hb hx) h

/-! ## Reachable states -/

/-- The states of the trace specification reachable from `TraceInit` by `TraceNext`: its initial state,
and every successor `Trace.next` gives of a reached state. A superset of the states `CheckTrace`'s search
looks at (`Trace.LineReach.reach`, `Trace.StepLineRel.reach`): it goes on past a violation, and through
successors the search drops as duplicates. -/
inductive Trace.Reach (tr : Trace) : TState → Prop
  | init : Trace.Reach tr tr.initState
  | step (f : TState) (tss : List TState) (s2 : TState) :
      Trace.Reach tr f → tr.next f = .ok tss → s2 ∈ tss → Trace.Reach tr s2

/-! ## The constants -/

/-- `b` has `a`'s constants. -/
def State.Frame (a b : State) : Prop :=
  b.server = a.server ∧ b.preVote = a.preVote ∧ b.checkQuorum = a.checkQuorum

theorem State.Frame.refl (a : State) : a.Frame a := ⟨rfl, rfl, rfl⟩

theorem State.Frame.trans {a b c : State} (h1 : a.Frame b) (h2 : b.Frame c) : a.Frame c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- A list's successors all have `a`'s constants. -/
def State.FrameAll (a : State) (l : List State) : Prop := ∀ s ∈ l, a.Frame s

theorem somes_frame {a : State} {l : List (Option State)} (h : ∀ o ∈ l, ∀ s, o = some s → a.Frame s) :
    a.FrameAll (somes l) := by
  intro s hs
  simp only [somes, List.mem_filterMap, id] at hs
  obtain ⟨o, ho, rfl⟩ := hs
  exact h _ ho s rfl

set_option hygiene false in
/-- An `Option`-valued action's successor: unfold, split, and the successor is built with `with`. -/
macro "frame_opt " f:ident : tactic => `(tactic| (
  unfold $f at h
  try dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> (repeat' split) <;> rfl)
    | (cases h; refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> (repeat' split) <;> rfl)))

set_option hygiene false in
/-- An `EvalM (Option State)`-valued action's successor. -/
macro "frame_eval " f:ident : tactic => `(tactic| (
  unfold $f at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; injection h with h; subst h; refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> (repeat' split) <;> rfl)
    | (cases h; refine ⟨?_, ?_, ?_⟩ <;> (try dsimp only) <;> (repeat' split) <;> rfl)))

theorem State.timeout_frame {st s : State} {i : ID} (h : st.timeout i = some s) : st.Frame s := by
  frame_opt State.timeout

theorem State.preTimeout_frame {st s : State} {i : ID} (h : st.preTimeout i = some s) : st.Frame s := by
  frame_opt State.preTimeout
theorem State.requestVote_frame {st s : State} {i j : ID} (h : st.requestVote i j = some s) : st.Frame s := by
  frame_opt State.requestVote
theorem State.requestPreVote_frame {st s : State} {i j : ID} (h : st.requestPreVote i j = some s) : st.Frame s := by
  frame_opt State.requestPreVote
theorem State.becomeLeader_frame {st s : State} {i : ID} (h : st.becomeLeader i = some s) : st.Frame s := by
  frame_opt State.becomeLeader
theorem State.clientRequest_frame {st s : State} {i : ID} {v : Int} (h : st.clientRequest i v = some s) :
    st.Frame s := by
  frame_opt State.clientRequest
theorem State.advanceCommitIndex_frame {st s : State} {i : ID} (h : st.advanceCommitIndex i = some s) :
    st.Frame s := by
  frame_opt State.advanceCommitIndex
theorem State.appendEntriesToSelf_frame {st s : State} {i : ID} (h : st.appendEntriesToSelf i = some s) :
    st.Frame s := by
  frame_opt State.appendEntriesToSelf
theorem State.ignoreInLease_frame {st s : State} {m : Msg} (h : st.ignoreInLease m = some s) : st.Frame s := by
  frame_opt State.ignoreInLease
theorem State.reconfigure_frame (st : State) (i : ID) (nc ln : SetIds) : st.Frame (st.reconfigure i nc ln) := by
  unfold State.reconfigure; split <;> exact ⟨rfl, rfl, rfl⟩
theorem State.addNewServer_frame {st s : State} {i j : ID} (h : st.addNewServer i j = some s) : st.Frame s := by
  unfold State.addNewServer at h; split at h
  · cases h
  · cases h; exact st.reconfigure_frame _ _ _
theorem State.addLearner_frame {st s : State} {i j : ID} (h : st.addLearner i j = some s) : st.Frame s := by
  unfold State.addLearner at h; split at h
  · cases h
  · cases h; exact st.reconfigure_frame _ _ _
theorem State.deleteServer_frame {st s : State} {i j : ID} (h : st.deleteServer i j = some s) : st.Frame s := by
  unfold State.deleteServer at h; split at h
  · cases h
  · cases h; exact st.reconfigure_frame _ _ _
theorem State.stepDownToFollower_frame {st s : State} {i : ID} (h : st.stepDownToFollower i = some s) :
    st.Frame s := by
  frame_opt State.stepDownToFollower
theorem State.ready_frame (st : State) (i : ID) : st.Frame (st.ready i) := ⟨rfl, rfl, rfl⟩
theorem State.restart_frame (st : State) (i : ID) : st.Frame (st.restart i) := ⟨rfl, rfl, rfl⟩
theorem State.appendEntriesInRangeToPeer_frame {st s : State} {sub : String} {i j : ID} {b e : Int}
    (h : st.appendEntriesInRangeToPeer sub i j b e = .ok (some s)) : st.Frame s := by
  frame_eval State.appendEntriesInRangeToPeer
theorem State.applySimpleConfChange_frame {st s : State} {i : ID}
    (h : st.applySimpleConfChange i = .ok (some s)) : st.Frame s := by
  frame_eval State.applySimpleConfChange

/-! ### The handlers -/

theorem State.updateTerm_frame {st s : State} {i j : ID} {m : Msg} (h : st.updateTerm i j m = some s) :
    st.Frame s := by
  frame_opt State.updateTerm
theorem State.dropStaleResponse_frame {st s : State} {i j : ID} {m : Msg} (h : st.dropStaleResponse i j m = some s) :
    st.Frame s := by
  frame_opt State.dropStaleResponse
theorem State.handleRequestVoteRequest_frame {st s : State} {i j : ID} {m : Msg}
    (h : st.handleRequestVoteRequest i j m = some s) : st.Frame s := by
  frame_opt State.handleRequestVoteRequest
theorem State.handleRequestVoteResponse_frame {st s : State} {i j : ID} {m : Msg}
    (h : st.handleRequestVoteResponse i j m = some s) : st.Frame s := by
  frame_opt State.handleRequestVoteResponse
theorem State.handlePreVoteRequest_frame (st : State) (i j : ID) (m : Msg) :
    st.Frame (st.handlePreVoteRequest i j m) := ⟨rfl, rfl, rfl⟩
theorem State.handlePreVoteResponse_frame {st s : State} {i j : ID} {m : Msg}
    (h : st.handlePreVoteResponse i j m = some s) : st.Frame s := by
  frame_opt State.handlePreVoteResponse
theorem State.rejectAppendEntriesRequest_frame {st s : State} {i j : ID} {m : Msg} {lo : Bool}
    (h : st.rejectAppendEntriesRequest i j m lo = some s) : st.Frame s := by
  frame_opt State.rejectAppendEntriesRequest
theorem State.returnToFollowerState_frame {st s : State} {i : ID} {m : Msg}
    (h : st.returnToFollowerState i m = some s) : st.Frame s := by
  frame_opt State.returnToFollowerState
theorem State.appendEntriesAlreadyDone_frame {st s : State} {i j : ID} {ix : Int} {m : Msg}
    (h : st.appendEntriesAlreadyDone i j ix m = some s) : st.Frame s := by
  frame_opt State.appendEntriesAlreadyDone
theorem State.conflictAppendEntriesRequest_frame {st s : State} {i : ID} {ix : Int} {m : Msg}
    (h : st.conflictAppendEntriesRequest i ix m = .ok (some s)) : st.Frame s := by
  frame_eval State.conflictAppendEntriesRequest
theorem State.noConflictAppendEntriesRequest_frame {st s : State} {i : ID} {ix : Int} {m : Msg}
    (h : st.noConflictAppendEntriesRequest i ix m = .ok (some s)) : st.Frame s := by
  frame_eval State.noConflictAppendEntriesRequest
theorem State.handleSnapshotRequest_frame {st s : State} {i j : ID} {m : Msg}
    (h : st.handleSnapshotRequest i j m = .ok (some s)) : st.Frame s := by
  frame_eval State.handleSnapshotRequest
theorem State.handleAppendEntriesResponse_frame {st s : State} {i j : ID} {m : Msg}
    (h : st.handleAppendEntriesResponse i j m = some s) : st.Frame s := by
  frame_opt State.handleAppendEntriesResponse

/-! ### Lists of successors -/

theorem frameAll_nil (a : State) : a.FrameAll [] := fun _ h => by simp at h

theorem frameAll_append {a : State} {l1 l2 : List State} (h1 : a.FrameAll l1) (h2 : a.FrameAll l2) :
    a.FrameAll (l1 ++ l2) := by
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem frameAll_single {a b : State} (h : a.Frame b) : a.FrameAll [b] := by
  intro s hs; simp at hs; subst hs; exact h

theorem frameAll_filter {a : State} {l : List State} {p : State → Bool} (h : a.FrameAll l) :
    a.FrameAll (l.filter p) := fun s hs => h s (List.mem_filter.1 hs).1

theorem frameAll_flatMap {α : Type} {a : State} {l : List α} {f : α → List State} (h : ∀ x ∈ l, a.FrameAll (f x)) :
    a.FrameAll (l.flatMap f) := by
  intro s hs; obtain ⟨x, hx, hs⟩ := List.mem_flatMap.1 hs; exact h x hx s hs

theorem frameAll_somes1 {a : State} {o : Option State} (h : ∀ s, o = some s → a.Frame s) : a.FrameAll (somes [o]) :=
  somes_frame (by intro o' ho s hs; simp at ho; subst ho; exact h s hs)

theorem frameAll_somes2 {a : State} {o1 o2 : Option State} (h1 : ∀ s, o1 = some s → a.Frame s)
    (h2 : ∀ s, o2 = some s → a.Frame s) : a.FrameAll (somes [o1, o2]) :=
  somes_frame (by
    intro o ho s hs; simp at ho
    rcases ho with rfl | rfl
    · exact h1 s hs
    · exact h2 s hs)

theorem State.acceptAppendEntriesRequest_frame {st : State} {i j : ID} {lo : Bool} {m : Msg} {l : List State}
    (h : st.acceptAppendEntriesRequest i j lo m = .ok l) : st.FrameAll l := by
  unfold State.acceptAppendEntriesRequest at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  split at h
  · cases h; exact frameAll_nil _
  · split at h
    · cases hs : st.handleSnapshotRequest i j m with
      | error e => rw [hs] at h; cases h
      | ok o =>
        rw [hs] at h; cases h
        exact frameAll_somes1 (fun s h' => State.handleSnapshotRequest_frame (by rw [hs, h']))
    · cases hc : st.conflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
      | error e => rw [hc] at h; cases h
      | ok c =>
        rw [hc] at h
        cases hn : st.noConflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
        | error e => rw [hn] at h; cases h
        | ok n =>
          rw [hn] at h; cases h
          refine somes_frame (fun o ho s hs => ?_)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl
          · exact State.appendEntriesAlreadyDone_frame hs
          · exact State.conflictAppendEntriesRequest_frame (by rw [hc, hs])
          · exact State.noConflictAppendEntriesRequest_frame (by rw [hn, hs])

theorem State.handleAppendEntriesRequest_frame {st : State} {i j : ID} {m : Msg} {l : List State}
    (h : st.handleAppendEntriesRequest i j m = .ok l) : st.FrameAll l := by
  have key : ∀ lo acc, st.acceptAppendEntriesRequest i j lo m = .ok acc →
      st.FrameAll (somes [st.rejectAppendEntriesRequest i j m lo, st.returnToFollowerState i m] ++ acc) :=
    fun lo acc ha => frameAll_append (frameAll_somes2 (fun s hs => State.rejectAppendEntriesRequest_frame hs)
      (fun s hs => State.returnToFollowerState_frame hs)) (State.acceptAppendEntriesRequest_frame ha)
  unfold State.handleAppendEntriesRequest at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  split at h
  · cases h; exact frameAll_nil _
  · cases ha : st.acceptAppendEntriesRequest i j _ m with
    | error e => rw [ha] at h; cases h
    | ok acc =>
      rw [ha] at h; cases h
      have hout := key _ _ ha
      split
      · intro s hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
        exact (hout t ht).trans ⟨rfl, rfl, rfl⟩
      · exact hout

theorem State.receive_frame {st : State} {m : Msg} {l : List State} (h : st.receive m = .ok l) : st.FrameAll l := by
  unfold State.receive at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  have hu : st.FrameAll (somes [st.updateTerm m.dest m.source m]) :=
    frameAll_somes1 (fun s hs => State.updateTerm_frame hs)
  split at h
  · cases h; exact frameAll_nil _
  · split at h
    · cases h; exact frameAll_append hu (frameAll_somes1 (fun s hs => State.handleRequestVoteRequest_frame hs))
    · cases h; exact frameAll_append hu (frameAll_somes2 (fun s hs => State.dropStaleResponse_frame hs)
        (fun s hs => State.handleRequestVoteResponse_frame hs))
    · cases ha : st.handleAppendEntriesRequest m.dest m.source m with
      | error e => rw [ha] at h; cases h
      | ok acc => rw [ha] at h; cases h; exact frameAll_append hu (State.handleAppendEntriesRequest_frame ha)
    · cases h; exact frameAll_append hu (frameAll_somes2 (fun s hs => State.dropStaleResponse_frame hs)
        (fun s hs => State.handleAppendEntriesResponse_frame hs))
    · cases h; exact frameAll_append hu (frameAll_single (State.handlePreVoteRequest_frame _ _ _ _))
    · cases h; exact frameAll_append hu (frameAll_somes2 (fun s hs => State.dropStaleResponse_frame hs)
        (fun s hs => State.handlePreVoteResponse_frame hs))

/-! ### The `IfLogged` actions -/

theorem Trace.requestVoteIfLogged_frame (tr : Trace) (ts : TState) (i j : ID) :
    ts.s.FrameAll (tr.requestVoteIfLogged ts i j) := by
  unfold Trace.requestVoteIfLogged
  split
  · exact frameAll_nil _
  · exact frameAll_filter (frameAll_somes2 (fun s hs => State.requestVote_frame hs)
      (fun s hs => State.requestPreVote_frame hs))

theorem Trace.becomeLeaderIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.becomeLeaderIfLogged ts i) := by
  unfold Trace.becomeLeaderIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.becomeLeader i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.becomeLeader_frame hb)
      · exact frameAll_nil _

theorem Trace.clientRequestIfLogged_frame (tr : Trace) (ts : TState) (i : ID) (v : Int) :
    ts.s.FrameAll (tr.clientRequestIfLogged ts i v) := by
  unfold Trace.clientRequestIfLogged
  split
  · exact frameAll_nil _
  · exact frameAll_somes1 (fun s hs => State.clientRequest_frame hs)

theorem Trace.advanceCommitIndexIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.advanceCommitIndexIfLogged ts i) := by
  unfold Trace.advanceCommitIndexIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.advanceCommitIndex i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.advanceCommitIndex_frame hb)
      · exact frameAll_nil _

theorem Trace.appendEntriesToSelfIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.appendEntriesToSelfIfLogged ts i) := by
  unfold Trace.appendEntriesToSelfIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.appendEntriesToSelf i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.appendEntriesToSelf_frame hb)
      · exact frameAll_nil _

theorem Trace.preTimeoutIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.preTimeoutIfLogged ts i) := by
  unfold Trace.preTimeoutIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.preTimeout i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.preTimeout_frame hb)
      · exact frameAll_nil _

theorem Trace.timeoutIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.timeoutIfLogged ts i) := by
  unfold Trace.timeoutIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.timeout i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.timeout_frame hb)
      · exact frameAll_nil _

theorem Trace.stepDownToFollowerIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.stepDownToFollowerIfLogged ts i) := by
  unfold Trace.stepDownToFollowerIfLogged
  split
  · exact frameAll_nil _
  · cases hb : ts.s.stepDownToFollower i with
    | none => exact frameAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact frameAll_single (State.stepDownToFollower_frame hb)
      · exact frameAll_nil _

theorem Trace.ignoreInLeaseIfLogged_frame (tr : Trace) (ts : TState) :
    ts.s.FrameAll (tr.ignoreInLeaseIfLogged ts) := by
  unfold Trace.ignoreInLeaseIfLogged
  split
  · exact frameAll_nil _
  · apply frameAll_flatMap
    intro m _
    split
    · exact frameAll_somes1 (fun s hs => State.ignoreInLease_frame hs)
    · exact frameAll_nil _

theorem Trace.changeConfIfLogged_frame (tr : Trace) (ts : TState) (i j : ID) (a : String) :
    ts.s.FrameAll (tr.changeConfIfLogged ts i j a) := by
  unfold Trace.changeConfIfLogged
  split
  · exact frameAll_nil _
  · split
    · try dsimp only
      split
      · exact frameAll_nil _
      · split
        · exact frameAll_somes1 (fun s hs => State.addNewServer_frame hs)
        · split
          · exact frameAll_somes1 (fun s hs => State.addLearner_frame hs)
          · split
            · exact frameAll_somes1 (fun s hs => State.deleteServer_frame hs)
            · exact frameAll_nil _
    · exact frameAll_nil _

theorem Trace.readyIfLogged_frame (tr : Trace) (ts : TState) (i : ID) :
    ts.s.FrameAll (tr.readyIfLogged ts i) := by
  unfold Trace.readyIfLogged
  split
  · exact frameAll_nil _
  · exact frameAll_single (State.ready_frame _ _)

theorem State.appendEntries_frame {st s : State} {i j : ID} {b e : Int}
    (h : st.appendEntries i j b e = .ok (some s)) : st.Frame s := State.appendEntriesInRangeToPeer_frame h
theorem State.heartbeat_frame {st s : State} {i j : ID} (h : st.heartbeat i j = .ok (some s)) : st.Frame s :=
  State.appendEntriesInRangeToPeer_frame h
theorem State.sendSnapshot_frame {st s : State} {i j : ID} {ix : Int} (h : st.sendSnapshot i j ix = .ok (some s)) :
    st.Frame s := State.appendEntriesInRangeToPeer_frame h

set_option hygiene false in
/-- An `EvalM (List State)`-valued `IfLogged` action's successors. -/
macro "frame_iflogged " f:ident : tactic => `(tactic| (
  unfold $f at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact frameAll_nil _)
    | (cases h; done)
    | (cases h; exact frameAll_single (State.appendEntries_frame ‹_›))
    | (cases h; exact frameAll_single (State.heartbeat_frame ‹_›))
    | (cases h; exact frameAll_single (State.sendSnapshot_frame ‹_›))
    | (cases h; exact frameAll_single (State.restart_frame _ _))
    | (cases h; exact somes_frame (by
        intro o ho s hs; simp at ho; subst ho; subst hs; exact State.applySimpleConfChange_frame ‹_›))))

theorem Trace.appendEntriesIfLogged_frame {tr : Trace} {ts : TState} {i j : ID} {b e : Int} {l : List State}
    (h : tr.appendEntriesIfLogged ts i j b e = .ok l) : ts.s.FrameAll l := by
  frame_iflogged Trace.appendEntriesIfLogged
theorem Trace.heartbeatIfLogged_frame {tr : Trace} {ts : TState} {i j : ID} {l : List State}
    (h : tr.heartbeatIfLogged ts i j = .ok l) : ts.s.FrameAll l := by
  frame_iflogged Trace.heartbeatIfLogged
theorem Trace.sendSnapshotIfLogged_frame {tr : Trace} {ts : TState} {i j : ID} {ix : Int} {l : List State}
    (h : tr.sendSnapshotIfLogged ts i j ix = .ok l) : ts.s.FrameAll l := by
  frame_iflogged Trace.sendSnapshotIfLogged
theorem Trace.restartIfLogged_frame {tr : Trace} {ts : TState} {i : ID} {l : List State}
    (h : tr.restartIfLogged ts i = .ok l) : ts.s.FrameAll l := by
  frame_iflogged Trace.restartIfLogged
theorem Trace.applySimpleConfChangeIfLogged_frame {tr : Trace} {ts : TState} {i : ID} {l : List State}
    (h : tr.applySimpleConfChangeIfLogged ts i = .ok l) : ts.s.FrameAll l := by
  frame_iflogged Trace.applySimpleConfChangeIfLogged

/-! ### `TraceNext` -/

/-- A fold in `EvalM` that appends successors keeps `FrameAll`. -/
theorem foldlM_frame {α : Type} {a : State} {l : List α} {f : List State → α → EvalM (List State)}
    (hf : ∀ acc x c, x ∈ l → a.FrameAll acc → f acc x = .ok c → a.FrameAll c) {b c : List State}
    (hb : a.FrameAll b) (h : l.foldlM f b = .ok c) : a.FrameAll c :=
  foldlM_except_inv (fun acc => a.FrameAll acc) f l b c hf hb h

theorem append_step_frame {a : State} {acc c r : List State} {x : EvalM (List State)}
    (hx : x = .ok r) (hr : a.FrameAll r) (hacc : a.FrameAll acc)
    (h : (do return acc ++ (← x) : EvalM (List State)) = .ok c) : a.FrameAll c := by
  rw [hx] at h
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h; exact frameAll_append hacc hr

theorem append_step_frame' {a : State} {acc c : List State} {x : EvalM (List State)}
    (hf : ∀ r, x = .ok r → a.FrameAll r) (hacc : a.FrameAll acc)
    (h : (do return acc ++ (← x) : EvalM (List State)) = .ok c) : a.FrameAll c := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok r => exact append_step_frame hx (hf r hx) hacc h

theorem skip_frame (a : State) (L : List State) (hL : a.FrameAll L) (b : Bool) :
    a.FrameAll (if b then L ++ [a] else L) := by
  split
  · exact frameAll_append hL (frameAll_single (State.Frame.refl _))
  · exact hL

theorem Trace.nonReceive_frame {tr : Trace} {ts : TState} {out : List State} (h : tr.nonReceive ts = .ok out) :
    ts.s.FrameAll out := by
  unfold Trace.nonReceive at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h
       try refine frameAll_append ?_ (frameAll_single (State.Frame.refl _))
       first
        | exact frameAll_nil _
        | (apply frameAll_flatMap; intro x _
           first
            | exact Trace.requestVoteIfLogged_frame _ _ _ _
            | exact Trace.becomeLeaderIfLogged_frame _ _ _
            | exact Trace.clientRequestIfLogged_frame _ _ _ _
            | exact Trace.advanceCommitIndexIfLogged_frame _ _ _
            | exact Trace.appendEntriesToSelfIfLogged_frame _ _ _
            | exact Trace.timeoutIfLogged_frame _ _ _
            | exact Trace.preTimeoutIfLogged_frame _ _ _
            | exact Trace.readyIfLogged_frame _ _ _
            | exact Trace.stepDownToFollowerIfLogged_frame _ _ _
            | (apply frameAll_flatMap; intro y _; exact Trace.changeConfIfLogged_frame _ _ _ _ _))
        | exact Trace.ignoreInLeaseIfLogged_frame _ _
        | (refine foldlM_frame ?_ (frameAll_nil _) ‹_›
           intro acc x c _ hacc hc
           try dsimp only at hc
           first
            | exact append_step_frame' (fun r hr => Trace.heartbeatIfLogged_frame hr) hacc hc
            | exact append_step_frame' (fun r hr => Trace.applySimpleConfChangeIfLogged_frame hr) hacc hc
            | exact append_step_frame' (fun r hr => Trace.restartIfLogged_frame hr) hacc hc
            | exact foldlM_frame (fun acc ix c _ hacc hc =>
                append_step_frame' (fun r hr => Trace.sendSnapshotIfLogged_frame hr) hacc hc) hacc hc
            | exact foldlM_frame (fun acc b c _ hacc hc => foldlM_frame (fun acc e c _ hacc hc =>
                append_step_frame' (fun r hr => Trace.appendEntriesIfLogged_frame hr) hacc hc) hacc hc) hacc hc))

/-- `receive`'s successors (`Trace.receive`) have the state's constants. -/
theorem Trace.receive_frame {tr : Trace} {ts : TState} {tss : List TState} (h : tr.receive ts = .ok tss) :
    ∀ x ∈ tss, ts.s.Frame x.s := by
  unfold Trace.receive at h
  dsimp only at h
  split at h
  · cases h; simp
  · refine foldlM_except_inv (fun acc : List TState => ∀ x ∈ acc, ts.s.Frame x.s) _ _ [] tss ?_ (by simp) h
    intro acc m c _ hacc hf
    repeat' split at hf
    all_goals first
      | (cases hf; exact hacc)
      | (revert hf
         cases hr : ts.s.receive m with
         | error e => intro hf; simp [Bind.bind, Except.bind] at hf
         | ok succ =>
           intro hf
           simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at hf
           subst hf
           intro x hx
           rcases List.mem_append.1 hx with hx | hx
           · exact hacc x hx
           · obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hx
             have := State.receive_frame hr s2 hs2
             split <;> exact this)

/-- `TraceNext`'s successors have the state's constants. -/
theorem Trace.next_frame {tr : Trace} {f : TState} {tss : List TState} (h : tr.next f = .ok tss) :
    ∀ x ∈ tss, f.s.Frame x.s := by
  unfold Trace.next at h
  split at h
  · cases h; simp
  · split at h
    · cases h; intro x hx; simp at hx; subst hx; exact State.Frame.refl _
    · simp only [Bind.bind, Except.bind] at h
      cases hn : tr.nonReceive f with
      | error e => rw [hn] at h; cases h
      | ok nr =>
        rw [hn] at h
        cases hr : tr.receive f with
        | error e => rw [hr] at h; cases h
        | ok rv =>
          rw [hr] at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hx; exact Trace.nonReceive_frame hn s2 hs2
          · exact Trace.receive_frame hr x hx

/-- Every reached state has `TraceInit`'s constants. -/
theorem Trace.Reach.frame {tr : Trace} {ts : TState} (h : tr.Reach ts) : tr.init.Frame ts.s := by
  induction h with
  | init => exact State.Frame.refl _
  | step f tss s2 _ hn hs ih => exact ih.trans (Trace.next_frame hn s2 hs)

/-- `newTraceWith`'s initial state has the trace's servers and the flags it was given. -/
theorem newTraceWith_init (events : List Event) (pv cq : Bool) (t : Trace) (h : newTraceWith events pv cq = .ok t) :
    t.init.server = t.server ∧ t.init.preVote = pv ∧ t.init.checkQuorum = cq := by
  unfold newTraceWith at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; exact ⟨rfl, rfl, rfl⟩)

/-- Every state the search of a trace `NewTrace` built can reach has the trace's servers, and
`PreVote` and `CheckQuorum` off. -/
theorem Trace.Valid.reach_frame {tr : Trace} (hv : tr.Valid) {ts : TState} (h : tr.Reach ts) :
    ts.s.server = tr.server ∧ ts.s.preVote = false ∧ ts.s.checkQuorum = false := by
  obtain ⟨evs, -, -, hnt⟩ := hv
  obtain ⟨h1, h2, h3⟩ := newTraceWith_init evs false false tr hnt
  obtain ⟨f1, f2, f3⟩ := h.frame
  exact ⟨f1.trans h1, f2.trans h2, f3.trans h3⟩

end Etcdraft
end EtcdGrove
end Perennial
