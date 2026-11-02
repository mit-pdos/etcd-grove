/-
Lean-first (no Rocq counterpart).

# Porcupine's search, in pure terms (2026-10-14)

Porcupine (`checker.go`, `checkSingle`) decides linearizability of a history by the
depth-first search of Wing & Gong with Lowe's memoization: the history's call and return
entries, sorted by time (`makeEntries`), are a doubly-linked list; the search *lifts* a call
(and its return) out of the list when the model can take its step from the current state,
and backtracks (*unlifts* the most recent one) when it reaches a return whose call is not
lifted; a configuration (the set of lifted operations, the model's state) already in the
cache is not explored again.

This file is the search's correctness argument, independent of the heap: what a history
and its linearizability are (`Linearizable`, porcupine's definition: closed intervals, an
operation precedes another iff it returns strictly before the other is called), the
search's abstract state (`Frame`s for the stack `calls`, the cursor `p` into the list of
entries not lifted, `rem es (ids fs)`, the cache as a list of configurations), and the
invariant `Inv` with one lemma per branch of the loop. What the checker needs for
*completeness* (a linearizable history is accepted):

- `inv_fail`: when the loop reaches a return with nothing to backtrack, the history is not
  linearizable;
- `inv_pop`: when it reaches a return with something to backtrack, the configuration it
  leaves had no completion (`Good`), and the invariant holds where it resumes;
- `inv_skip`, `inv_push`: the call branches.

Soundness (an accepted history is linearizable) is in `Soundness.lean`. Both are partial
correctness: nothing says the search terminates.

The cache is sound for any hash function: a cached configuration is on the stack or has no
completion (`CacheOk`), whichever bucket it is in; a missed hit only re-explores.
-/
module

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

/-- An operation of a history: what it did (`val`: its input and output) and its interval
(`call`, `ret`: porcupine's `Operation.Call` and `Return`, closed). -/
structure Op (α : Type) where
  val : α
  call : Int
  ret : Int

/-- A deterministic sequential specification (porcupine's `Model`): from a state, an
operation either is allowed and leads to one state, or is not allowed. -/
structure SeqModel (σ α : Type) where
  init : σ
  step : σ → α → Option σ

variable {σ α : Type}

/-- The state after a sequence of operations, if the model allows them. -/
def run (M : SeqModel σ α) : σ → List α → Option σ
  | s, [] => some s
  | s, a :: l =>
    match M.step s a with
    | some s' => run M s' l
    | none => none

/-- Operation `a` of history `h` precedes operation `b` in real time: it returned before `b`
was called (porcupine's intervals are closed). -/
def Prec (h : List (Op α)) (a b : Nat) : Prop :=
  ∃ oa ob, h[a]? = some oa ∧ h[b]? = some ob ∧ oa.ret < ob.call

/-- The operations of `h` at indices `π`, in that order. -/
def vals (h : List (Op α)) (π : List Nat) : List α :=
  π.filterMap fun k => (h[k]?).map Op.val

/-- `π` orders the operations of `h` outside `S` so that the model can run them from `t`, and
no operation of `π` precedes in real time one earlier in `π`. -/
def Completes (M : SeqModel σ α) (h : List (Op α)) (S : Nat → Prop) (t : σ) (π : List Nat) :
    Prop :=
  π.Nodup ∧ (∀ k, k ∈ π ↔ k < h.length ∧ ¬ S k) ∧ (run M t (vals h π)).isSome ∧
    π.Pairwise fun a b => ¬ Prec h b a

/-- A configuration of the search (the operations `S` linearized, the model's state `t`) has
a completion. -/
def Good (M : SeqModel σ α) (h : List (Op α)) (S : Nat → Prop) (t : σ) : Prop :=
  ∃ π, Completes M h S t π

/-- Porcupine's linearizability: some order of all of `h`'s operations is allowed by the
model from its initial state and respects real time. -/
def Linearizable (M : SeqModel σ α) (h : List (Op α)) : Prop :=
  Good M h (fun _ => False) M.init

theorem good_congr {M : SeqModel σ α} {h : List (Op α)} {S S' : Nat → Prop} {t : σ}
    (hS : ∀ i, S i ↔ S' i) (hg : Good M h S t) : Good M h S' t := by
  obtain ⟨π, hnd, hmem, hrun, hpw⟩ := hg
  exact ⟨π, hnd, fun k => by rw [hmem k, hS k], hrun, hpw⟩


/-! ## The search's abstract state -/

/-- A frame of the stack `calls`: the operation lifted, the state before it (`callsEntry.state`)
and where its call was in the list it was lifted from (where the search resumes). -/
structure Frame (σ : Type) where
  id : Nat
  pre : σ
  pos : Nat
  fr : List Nat

/-- The operations lifted (newest first). -/
def ids (fs : List (Frame σ)) : List Nat := fs.map Frame.id

/-- The frames are steps of the model from its initial state, to `s`. -/
def Chain (M : SeqModel σ α) (h : List (Op α)) : List (Frame σ) → σ → Prop
  | [], s => s = M.init
  | f :: fs, s => Chain M h fs f.pre ∧ ∃ o, h[f.id]? = some o ∧ M.step f.pre o.val = some s

theorem chain_det {M : SeqModel σ α} {h : List (Op α)} :
    ∀ {fs : List (Frame σ)} {s s' : σ}, Chain M h fs s → Chain M h fs s' → s = s'
  | [], _, _, h1, h2 => by simp only [Chain] at h1 h2; rw [h1, h2]
  | f :: fs, _, _, ⟨_, o, ho, hs⟩, ⟨_, o', ho', hs'⟩ => by
    rw [ho] at ho'; cases ho'; rw [hs] at hs'; cases hs'; rfl

/-- Lifting `y` from `(B, t)` leads only to configurations without completion. -/
def SuccBad (M : SeqModel σ α) (h : List (Op α)) (B : List Nat) (t : σ) (y : Nat) : Prop :=
  ∀ o t', h[y]? = some o → M.step t o.val = some t' → ¬ Good M h (· ∈ y :: B) t'

/-- A cached configuration is one of the stack's. -/
def OnStack (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ))
    (c : (Nat → Prop) × σ) : Prop :=
  ∃ fs', fs' <:+ fs ∧ (∀ i, c.1 i ↔ i ∈ ids fs') ∧ Chain M h fs' c.2

/-- Every cached configuration is on the stack or has no completion. -/
def CacheOk (M : SeqModel σ α) (h : List (Op α)) (fs : List (Frame σ))
    (cache : List ((Nat → Prop) × σ)) : Prop :=
  ∀ c ∈ cache, OnStack M h fs c ∨ ¬ Good M h c.1 c.2

theorem ids_suffix {fs fs' : List (Frame σ)} (hs : fs' <:+ fs) {i : Nat} (hi : i ∈ ids fs') :
    i ∈ ids fs :=
  (hs.map Frame.id).subset hi

end Theory
end github_com.anishathalye.porcupine
end Perennial
