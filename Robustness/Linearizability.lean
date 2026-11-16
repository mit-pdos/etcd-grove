/-
Linearizability of a trace of operation events [Trusted definitions!]: the guarantee of a
robustness statement about a service whose clients call operations.

An operation is named by a key `k : K` (its identity: a client's retries of one operation carry
the same key); a trace is its calls and returns, each at a time (`OpEv`). A trace from a real
network has calls that never return (the client gave up, the connection broke, the server crashed)
and operations called several times (retries, at the same or another server) or answered several
times; so `LinearizableTrace M h` says:

* **well formed** (`WellFormed`): every return follows a call of its key; all calls of a key carry
  one input, and all its returns one output (a retried operation is one operation, whose answers
  agree);
* **linearizable** (Herlihy and Wing, with pending operations): each operation, as the interval
  from its first call to its first return, with its input and output, and some of the operations
  that never returned, each with some output and an interval open to the end of the trace, are
  linearizable by porcupine's definition (`Theory.Linearizable`: some order of them that the
  sequential model `M` allows from its initial state, in which no operation comes before one that
  returned before it was called). Operations that never returned and are left out took no effect.

Porcupine's checker decides the same definition on complete histories (its soundness and
completeness: `Proof/github_com/anishathalye/porcupine/`); this one is its extension to pending
operations, as a test's history with timed-out calls is checked (`examples/lib/lintest`).
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open github_com.anishathalye.porcupine

/-- A call of operation `k` with input `i`, or a return of `k` with output `o`. -/
inductive OpEv (K I O : Type) where
  | call (k : K) (i : I)
  | ret (k : K) (o : O)

variable {K I O σ : Type} [DecidableEq K]

/-- The time and input of the first call of `k` in `h`. -/
def firstCall (h : List (Nat × OpEv K I O)) (k : K) : Option (Nat × I) :=
  h.findSome? fun
    | (t, .call k' i) => if k' = k then some (t, i) else none
    | _ => none

/-- The time and output of the first return of `k` in `h`. -/
def firstRet (h : List (Nat × OpEv K I O)) (k : K) : Option (Nat × O) :=
  h.findSome? fun
    | (t, .ret k' o) => if k' = k then some (t, o) else none
    | _ => none

/-- The keys called in `h`, each once. -/
def calledKeys (h : List (Nat × OpEv K I O)) : List K :=
  (h.filterMap fun
    | (_, .call k _) => some k
    | _ => none).eraseDups

/-- A time after every event of `h`. -/
def horizon (h : List (Nat × OpEv K I O)) : Nat := h.foldr (fun x m => max x.1 m) 0 + 1

/-- `h` is well formed: every return follows a call of its key; a key's calls carry one input,
its returns one output. -/
def WellFormed (h : List (Nat × OpEv K I O)) : Prop :=
  (∀ t k o, (t, OpEv.ret k o) ∈ h → ∃ t' i, (t', OpEv.call k i) ∈ h ∧ t' ≤ t) ∧
  (∀ t t' k i i', (t, OpEv.call k i) ∈ h → (t', OpEv.call k i') ∈ h → i = i') ∧
  (∀ t t' k o o', (t, OpEv.ret k o) ∈ h → (t', OpEv.ret k o') ∈ h → o = o')

/-- The history of `h` as porcupine's operations, with `pend` choosing which operations that never
returned took effect and with which output: each called key's input and output, from its first
call to its first return (or to `horizon h`, for a pending one `pend` keeps). -/
def history (h : List (Nat × OpEv K I O)) (pend : K → Option O) : List (Theory.Op (I × O)) :=
  (calledKeys h).filterMap fun k =>
    match firstCall h k with
    | none => none
    | some (tc, i) =>
      match firstRet h k with
      | some (tr, o) => some ⟨(i, o), (tc : Int), (tr : Int)⟩
      | none => (pend k).map fun o => ⟨(i, o), (tc : Int), (horizon h : Int)⟩

/-- **The trace `h` is linearizable for the sequential model `M`** (see the file header). -/
def LinearizableTrace (M : Theory.SeqModel σ (I × O)) (h : List (Nat × OpEv K I O)) : Prop :=
  WellFormed h ∧ ∃ pend : K → Option O, Theory.Linearizable M (history h pend)

/-! ## Sanity -/

/-- The empty trace is linearizable. -/
theorem linearizableTrace_nil (M : Theory.SeqModel σ (I × O)) :
    LinearizableTrace M ([] : List (Nat × OpEv K I O)) := by
  refine ⟨⟨by simp, by simp, by simp⟩, fun _ => none, [], ?_⟩
  simp [Theory.Completes, history, calledKeys, Theory.vals, Theory.run]

end Robustness
end Perennial
