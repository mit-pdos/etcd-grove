/-
Lean-first (no Rocq counterpart).

# linkv: the porcupine model of a key-value store with failed writes (2026-10-19)

The sequential model the `lintest` instance over etcd's client checks against (D20, part (c)):
operations `Put(k, v)` and `Get(k)` (`KVIn`), whose outputs (`KVOut`) are `ok` (a put),
`okGet r` (a get that read `r`: the key's value, or none) or `err` (the call returned an error).

## An error's effect is unknown, and may come late

A put that returned an error may have been applied, or not; and when it was, it may have been
applied *after* the call returned (the client gave up on the reply, a timeout, while the
proposal was still in raft: the server applies it later). etcd's robustness checker handles
both: its model is nondeterministic (`tests/robustness/model/non_deterministic.go`: the state is
the list of the states the history may have reached, and a failed request keeps each state and
adds its successor), and a failed request's return time is set to infinity before porcupine
checks the history (`validate/validate.go`, `prepareAndCategorizeOperations`). `lintest.Run`
passes porcupine the return time the clock read, so a model that only lets a failed put take
effect within its call would reject a correct history (a failed put, then a get that does not see
it, then a get that does). This model puts the late effect in the state instead: a failed put
leaves the put **pending** (`Cfg.pend`), and a pending put may take effect at any later time, at
most once (`Silent`: the server applies the proposal it got once, part (b)), or never.

## Why a set of configurations (`KVSet`)

`SeqModel.step` is a function (`σ → α → Option σ`), and `lintest`'s generic theorem is over it;
a nondeterministic step would change the theory. So the model's state is the **set of
configurations** the history may have reached (`KVSet`), the powerset construction of the
nondeterministic model, as etcd's own model does: `kvSeq.step S (i, o)` is the set of
configurations reachable from a configuration of `S` by any pending puts taking effect, then the
operation `(i, o)` (`CStep`), then any pending puts taking effect again (`post`), and `none`
when it is empty (the history is not allowed). The alternatives:

- *an output naming the choice* ("error, applied" / "error, not applied"): the output is the Go
  value the closure returns and porcupine sees; the closure does not know which happened;
- *a state carrying a prophesied choice*: a deterministic step needs the choice as part of the
  state or the operation, which porcupine's Go model would then need too; and the choice's time
  (a late effect) is not one value;
- *a set of configurations*: no change to `lintest`, and the Go model is etcd's shape (a list of
  states, `Equal` on lists). At a commit, the proof steps the real configuration (`CStep`), which
  is in the set (`kvSeq_step_of_cstep`); a late effect is a step of the real configuration
  within the set (`KVSet.Closed`, `Closed.reach`), with no operation of the log.

A failed get changes nothing and constrains nothing (etcd's checker drops failed reads from the
linearization, `isLinearizable`). Keys and values are any types with decidable equality; the
instance takes etcd's `GoString`s (`ModelKV.lean`). Values only: no revisions (etcd's model also
checks them; a later refinement).

`kvM dec` is the model on porcupine's operations `α` (the instance: `OpV`, pairs of Go interface
values) through a decoder `dec` of the Go input and output types, fixed by the translation of
the Go program (`examples/linkv/linkv.go`: `Input`, `Output`); an operation `dec` rejects is not
allowed.
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace linkv

open github_com.anishathalye.porcupine.Theory

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- An operation's input. -/
inductive KVIn (K V : Type) where
  | put (k : K) (v : V)
  | get (k : K)

/-- An operation's output: a put's `ok`, a get's value (none: the key is absent), or an error. -/
inductive KVOut (V : Type) where
  | ok
  | okGet (r : Option V)
  | err

/-- A store: every key's value, if any. -/
abbrev Store (K V : Type) := K → Option V

/-- The store after writing `v` at `k`. -/
def Store.set (m : Store K V) (k : K) (v : V) : Store K V :=
  fun k' => if k' = k then some v else m k'

/-- A configuration: the store, and the failed puts that may still take effect. -/
structure Cfg (K V : Type) where
  kv : Store K V
  pend : List (K × V)

/-- A pending put takes effect (once: it leaves the pending list). -/
inductive Silent : Cfg K V → Cfg K V → Prop where
  | apply (c : Cfg K V) (k : K) (v : V) (h : (k, v) ∈ c.pend) :
      Silent c ⟨c.kv.set k v, c.pend.erase (k, v)⟩

/-- Any number of pending puts take effect. -/
inductive Reach : Cfg K V → Cfg K V → Prop where
  | refl (c : Cfg K V) : Reach c c
  | step {c c₁ c₂ : Cfg K V} : Silent c c₁ → Reach c₁ c₂ → Reach c c₂

/-- **One operation on a configuration**: a put that returned `ok` takes effect; a put that
failed becomes pending; a get that read `r` finds `r` at its key; a failed get does nothing. -/
inductive CStep : Cfg K V → KVIn K V → KVOut V → Cfg K V → Prop where
  | putOk (c : Cfg K V) (k : K) (v : V) : CStep c (.put k v) .ok ⟨c.kv.set k v, c.pend⟩
  | putErr (c : Cfg K V) (k : K) (v : V) : CStep c (.put k v) .err ⟨c.kv, (k, v) :: c.pend⟩
  | getOk (c : Cfg K V) (k : K) : CStep c (.get k) (.okGet (c.kv k)) c
  | getErr (c : Cfg K V) (k : K) : CStep c (.get k) .err c

/-- The model's state: the configurations the history may have reached. -/
abbrev KVSet (K V : Type) := Cfg K V → Prop

/-- The configurations after `(i, o)` from `S` (see the file header). -/
def post (S : KVSet K V) (i : KVIn K V) (o : KVOut V) : KVSet K V :=
  fun c' => ∃ c₀ c c₁, S c₀ ∧ Reach c₀ c ∧ CStep c i o c₁ ∧ Reach c₁ c'

/-- The initial state: the empty store, nothing pending. -/
def kvInit : KVSet K V := fun c => c = ⟨fun _ => none, []⟩

open Classical in
/-- **The sequential model** on abstract operations (see the file header). -/
noncomputable def kvSeq : SeqModel (KVSet K V) (KVIn K V × KVOut V) where
  init := kvInit
  step S io := if ∃ c, post S io.1 io.2 c then some (post S io.1 io.2) else none

/-- **The model on porcupine's operations** `α`, through the decoder `dec`. -/
noncomputable def kvM {α : Type} (dec : α → Option (KVIn K V × KVOut V)) :
    SeqModel (KVSet K V) α where
  init := kvInit
  step S a := (dec a).bind (kvSeq.step S)

theorem kvM_step {α : Type} (dec : α → Option (KVIn K V × KVOut V)) (S : KVSet K V) (a : α)
    (i : KVIn K V) (o : KVOut V) (h : dec a = some (i, o)) :
    (kvM dec).step S a = kvSeq.step S (i, o) := by
  simp [kvM, h]

/-! ## The lemmas the instance's proof needs -/

theorem Reach.trans {c₁ c₂ c₃ : Cfg K V} (h₁ : Reach c₁ c₂) (h₂ : Reach c₂ c₃) : Reach c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem Reach.single {c c' : Cfg K V} (h : Silent c c') : Reach c c' := .step h (.refl _)

/-- **A commit**: the real configuration `c` is in `S` and steps by `(i, o)` to `c₁` (and then
by pending puts to `c'`); the model allows `(i, o)`, and its next state holds `c'`. -/
theorem kvSeq_step_of_cstep {S : KVSet K V} {c c₁ c' : Cfg K V} {i : KVIn K V} {o : KVOut V}
    (hS : S c) (h : CStep c i o c₁) (hr : Reach c₁ c') :
    ∃ S', kvSeq.step S (i, o) = some S' ∧ S' c' := by
  have hp : post S i o c' := ⟨c, c, c₁, hS, .refl _, h, hr⟩
  refine ⟨post S i o, ?_, hp⟩
  simp only [kvSeq]
  split
  · rfl
  · next hn => exact absurd ⟨c', hp⟩ hn

/-- What the model's next state is, when it allows `(i, o)`. -/
theorem kvSeq_step_some {S S' : KVSet K V} {i : KVIn K V} {o : KVOut V}
    (h : kvSeq.step S (i, o) = some S') : S' = post S i o := by
  simp only [kvSeq] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A state is closed under late effects. -/
def KVSet.Closed (S : KVSet K V) : Prop := ∀ c c', S c → Reach c c' → S c'

/-- **A late effect**: a pending put of the real configuration takes effect, within the set. -/
theorem KVSet.Closed.reach {S : KVSet K V} (hS : S.Closed) {c c' : Cfg K V} (hc : S c)
    (h : Reach c c') : S c' := hS c c' hc h

theorem kvInit_closed : (kvInit : KVSet K V).Closed := by
  intro c c' hc h
  subst hc
  cases h with
  | refl => rfl
  | step hs _ => cases hs with | apply _ _ hm => cases hm

theorem post_closed (S : KVSet K V) (i : KVIn K V) (o : KVOut V) : (post S i o).Closed := by
  rintro c c' ⟨c₀, c₂, c₁, h0, hr0, hs, hr1⟩ h
  exact ⟨c₀, c₂, c₁, h0, hr0, hs, hr1.trans h⟩

/-- Every state the model reaches is closed. -/
theorem kvSeq_step_closed {S S' : KVSet K V} {i : KVIn K V} {o : KVOut V}
    (h : kvSeq.step S (i, o) = some S') : S'.Closed := by
  rw [kvSeq_step_some h]; exact post_closed S i o

/-- A put that returned `ok`, at the real configuration `c ∈ S`. -/
theorem kvSeq_putOk {S : KVSet K V} {c : Cfg K V} (hS : S c) (k : K) (v : V) :
    ∃ S', kvSeq.step S (.put k v, .ok) = some S' ∧ S' ⟨c.kv.set k v, c.pend⟩ :=
  kvSeq_step_of_cstep hS (.putOk c k v) (.refl _)

/-- A put that failed, having taken effect at the commit (the server applied it during the
call): pending, then applied. -/
theorem kvSeq_putErr_applied {S : KVSet K V} {c : Cfg K V} (hS : S c) (k : K) (v : V) :
    ∃ S', kvSeq.step S (.put k v, .err) = some S' ∧ S' ⟨c.kv.set k v, c.pend⟩ := by
  refine kvSeq_step_of_cstep hS (.putErr c k v) (.single ?_)
  have h := Silent.apply ⟨c.kv, (k, v) :: c.pend⟩ k v List.mem_cons_self
  simpa [List.erase_cons_head] using h

/-- A put that failed, not (yet) applied at the commit (the call's return): pending. -/
theorem kvSeq_putErr_pending {S : KVSet K V} {c : Cfg K V} (hS : S c) (k : K) (v : V) :
    ∃ S', kvSeq.step S (.put k v, .err) = some S' ∧ S' ⟨c.kv, (k, v) :: c.pend⟩ :=
  kvSeq_step_of_cstep hS (.putErr c k v) (.refl _)

/-- A get that read the real configuration's value. -/
theorem kvSeq_getOk {S : KVSet K V} {c : Cfg K V} (hS : S c) (k : K) :
    ∃ S', kvSeq.step S (.get k, .okGet (c.kv k)) = some S' ∧ S' c :=
  kvSeq_step_of_cstep hS (.getOk c k) (.refl _)

/-- A failed get. -/
theorem kvSeq_getErr {S : KVSet K V} {c : Cfg K V} (hS : S c) (k : K) :
    ∃ S', kvSeq.step S (.get k, .err) = some S' ∧ S' c :=
  kvSeq_step_of_cstep hS (.getErr c k) (.refl _)

/-- A pending put takes effect late (no operation of the log). -/
theorem KVSet.Closed.apply {S : KVSet K V} (hS : S.Closed) {c : Cfg K V} (hc : S c) {k : K} {v : V}
    (hm : (k, v) ∈ c.pend) : S ⟨c.kv.set k v, c.pend.erase (k, v)⟩ :=
  hS.reach hc (.single (.apply c k v hm))

/-! ## Sanity: the history of the file header is allowed -/

/-- A failed put of `k ↦ v`, a get of `k` not seeing it, a get seeing it: allowed (`run` reaches
a state), with the put taking effect between the gets. -/
example (k : K) (v : V) :
    (run kvSeq kvInit [(.put k v, .err), (.get k, .okGet none), (.get k, .okGet (some v))]).isSome := by
  have h0 : (kvInit : KVSet K V) ⟨fun _ => none, []⟩ := rfl
  obtain ⟨S1, h1, m1⟩ := kvSeq_putErr_pending h0 k v
  obtain ⟨S2, h2, m2⟩ := kvSeq_getOk m1 k
  have m2' : S2 ⟨Store.set (fun _ => none) k v, []⟩ := by
    have := (kvSeq_step_closed h2).apply m2 (k := k) (v := v) List.mem_cons_self
    simpa [List.erase_cons_head] using this
  obtain ⟨S3, h3, -⟩ := kvSeq_getOk m2' k
  simp only [Store.set, ite_true] at h3
  simp [run, h1, h2, h3]

end linkv
end EtcdGrove
end Perennial
