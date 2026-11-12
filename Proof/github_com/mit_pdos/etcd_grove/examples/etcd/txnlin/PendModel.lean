/-
Lean-first (no Rocq counterpart).

# linkv: a deterministic store with failed writes, as a porcupine model (linkv-txn stage C)

The construction of linkv's `KVModel.lean` (2026-10-19, values-only puts and gets; linkv retired,
D34), generic: a deterministic sequential store (`step : I → St → St × O`, the operation's effect and its answer)
whose writes (`isWrite`) may fail with an unknown effect. A write that returned an error may
have taken effect, or not, and possibly *after* its call returned (the proposal still in raft:
linkv's `KVModel.lean` header, etcd's robustness checker's `NonDeterministicModel` and its infinite
return times); a failed write is left **pending** and may take effect at any later time, at most
once, or never (`Silent`); a failed read constrains nothing. `SeqModel.step` is a function, so
the model's state is the **set of configurations** the history may have reached (`PSet`, the
powerset construction): `pSeq.step S (i, o)` is the configurations reachable from `S`'s by
pending writes, then `(i, o)` (`PStep`), then pending writes again. `lintest`'s theorem applies
unchanged. An answer is `ok o` (the call returned `o`) or `err`.

`TxnModel.lean` instantiates it with etcd's KV operations (gets, lists, puts, deletes, flat
transactions, every answer with its revision).
Moved from `examples/linkv/` when linkv was retired (2026-10-22, `notes/decisions.md` D34); the
names keep their namespace `linkv`.
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace linkv

open github_com.anishathalye.porcupine.Theory

/-- A call's answer: its output, or an error. -/
inductive Ans (O : Type) where
  | ok (o : O)
  | err

variable {St I O : Type} [DecidableEq I]

/-- **A store with failed writes**: its states' initial one, the deterministic step, and which
inputs are writes (a failed write may take effect later; a failed read constrains nothing). -/
structure PendSpec (St I O : Type) where
  init : St
  step : I → St → St × O
  isWrite : I → Bool

variable (P : PendSpec St I O)

/-- A configuration: the store, and the failed writes that may still take effect. -/
structure PCfg (St I : Type) where
  st : St
  pend : List I

/-- A pending write takes effect (once: it leaves the pending list); or the pending list is
reordered (a multiset: the Go model may keep it in any order). -/
inductive PSilent : PCfg St I → PCfg St I → Prop where
  | apply (c : PCfg St I) (i : I) (h : i ∈ c.pend) :
      PSilent c ⟨(P.step i c.st).1, c.pend.erase i⟩
  | perm (c : PCfg St I) (p : List I) (h : p.Perm c.pend) : PSilent c ⟨c.st, p⟩

/-- Any number of pending writes take effect. -/
inductive PReach : PCfg St I → PCfg St I → Prop where
  | refl (c : PCfg St I) : PReach c c
  | step {c c₁ c₂ : PCfg St I} : PSilent P c c₁ → PReach c₁ c₂ → PReach c c₂

/-- **One operation on a configuration**: a call that returned `o` takes effect and answered the
step's output; a failed write becomes pending; a failed read does nothing. -/
inductive PStep : PCfg St I → I → Ans O → PCfg St I → Prop where
  | ok (c : PCfg St I) (i : I) : PStep c i (.ok (P.step i c.st).2) ⟨(P.step i c.st).1, c.pend⟩
  | errW (c : PCfg St I) (i : I) (h : P.isWrite i = true) : PStep c i .err ⟨c.st, i :: c.pend⟩
  | errR (c : PCfg St I) (i : I) (h : P.isWrite i = false) : PStep c i .err c

/-- The model's state: the configurations the history may have reached. -/
abbrev PSet (St I : Type) := PCfg St I → Prop

/-- The configurations after `(i, o)` from `S`. -/
def ppost (S : PSet St I) (i : I) (o : Ans O) : PSet St I :=
  fun c' => ∃ c₀ c c₁, S c₀ ∧ PReach P c₀ c ∧ PStep P c i o c₁ ∧ PReach P c₁ c'

/-- The initial state: the initial store, nothing pending. -/
def pInit : PSet St I := fun c => c = ⟨P.init, []⟩

open Classical in
/-- **The sequential model** on abstract operations. -/
noncomputable def pSeq : SeqModel (PSet St I) (I × Ans O) where
  init := pInit P
  step S io := if ∃ c, ppost P S io.1 io.2 c then some (ppost P S io.1 io.2) else none

/-- **The model on porcupine's operations** `α`, through the decoder `dec`. -/
noncomputable def pM {α : Type} (dec : α → Option (I × Ans O)) : SeqModel (PSet St I) α where
  init := pInit P
  step S a := (dec a).bind ((pSeq P).step S)

theorem pM_step {α : Type} (dec : α → Option (I × Ans O)) (S : PSet St I) (a : α) (i : I)
    (o : Ans O) (h : dec a = some (i, o)) : (pM P dec).step S a = (pSeq P).step S (i, o) := by
  simp [pM, h]

/-! ## The lemmas an instance's proof needs -/

variable {P}

theorem PReach.trans {c₁ c₂ c₃ : PCfg St I} (h₁ : PReach P c₁ c₂) (h₂ : PReach P c₂ c₃) :
    PReach P c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem PReach.single {c c' : PCfg St I} (h : PSilent P c c') : PReach P c c' := .step h (.refl _)

/-- **A commit**: the real configuration `c` is in `S` and steps by `(i, o)` to `c₁` (then by
pending writes to `c'`); the model allows `(i, o)`, and its next state holds `c'`. -/
theorem pSeq_step_of_pstep {S : PSet St I} {c c₁ c' : PCfg St I} {i : I} {o : Ans O}
    (hS : S c) (h : PStep P c i o c₁) (hr : PReach P c₁ c') :
    ∃ S', (pSeq P).step S (i, o) = some S' ∧ S' c' := by
  have hp : ppost P S i o c' := ⟨c, c, c₁, hS, .refl _, h, hr⟩
  refine ⟨ppost P S i o, ?_, hp⟩
  simp only [pSeq]
  split
  · rfl
  · next hn => exact absurd ⟨c', hp⟩ hn

/-- What the model's next state is, when it allows `(i, o)`. -/
theorem pSeq_step_some {S S' : PSet St I} {i : I} {o : Ans O}
    (h : (pSeq P).step S (i, o) = some S') : S' = ppost P S i o := by
  simp only [pSeq] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A state is closed under late effects. -/
def PSet.Closed (P : PendSpec St I O) (S : PSet St I) : Prop :=
  ∀ c c', S c → PReach P c c' → S c'

theorem pInit_closed_of (h : ∀ c c' : PCfg St I, c = ⟨P.init, []⟩ → PSilent P c c' →
    c' = ⟨P.init, []⟩) : PSet.Closed P (pInit P) := by
  intro c c' hc hr
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (h _ _ hc hs)

/-- The initial state is closed (nothing is pending). -/
theorem pInit_closed : PSet.Closed P (pInit P) := by
  apply pInit_closed_of
  intro c c' hc hs
  subst hc
  cases hs with
  | apply _ hm => cases hm
  | perm p hp => simp only at hp; rw [List.Perm.eq_nil hp]

theorem ppost_closed (S : PSet St I) (i : I) (o : Ans O) : PSet.Closed P (ppost P S i o) := by
  rintro c c' ⟨c₀, c₂, c₁, h0, hr0, hs, hr1⟩ h
  exact ⟨c₀, c₂, c₁, h0, hr0, hs, hr1.trans h⟩

/-- Every state the model reaches is closed. -/
theorem pSeq_step_closed {S S' : PSet St I} {i : I} {o : Ans O}
    (h : (pSeq P).step S (i, o) = some S') : PSet.Closed P S' := by
  rw [pSeq_step_some h]; exact ppost_closed S i o

/-- A call that returned its output, at the real configuration `c ∈ S`. -/
theorem pSeq_ok {S : PSet St I} {c : PCfg St I} (hS : S c) (i : I) :
    ∃ S', (pSeq P).step S (i, .ok (P.step i c.st).2) = some S' ∧
      S' ⟨(P.step i c.st).1, c.pend⟩ :=
  pSeq_step_of_pstep hS (.ok c i) (.refl _)

/-- A write that failed, having taken effect at the commit (the server applied it during the
call): pending, then applied. -/
theorem pSeq_errW_applied {S : PSet St I} {c : PCfg St I} (hS : S c) (i : I)
    (hw : P.isWrite i = true) :
    ∃ S', (pSeq P).step S (i, .err) = some S' ∧ S' ⟨(P.step i c.st).1, c.pend⟩ := by
  refine pSeq_step_of_pstep hS (.errW c i hw) (.single ?_)
  have h := PSilent.apply (P := P) ⟨c.st, i :: c.pend⟩ i List.mem_cons_self
  simpa [List.erase_cons_head] using h

/-- A write that failed, not (yet) applied at the commit (the call's return): pending. -/
theorem pSeq_errW_pending {S : PSet St I} {c : PCfg St I} (hS : S c) (i : I)
    (hw : P.isWrite i = true) :
    ∃ S', (pSeq P).step S (i, .err) = some S' ∧ S' ⟨c.st, i :: c.pend⟩ :=
  pSeq_step_of_pstep hS (.errW c i hw) (.refl _)

/-- A read that failed. -/
theorem pSeq_errR {S : PSet St I} {c : PCfg St I} (hS : S c) (i : I) (hw : P.isWrite i = false) :
    ∃ S', (pSeq P).step S (i, .err) = some S' ∧ S' c :=
  pSeq_step_of_pstep hS (.errR c i hw) (.refl _)

/-- A pending write takes effect late (no operation of the log). -/
theorem PSet.Closed.apply {S : PSet St I} (hS : PSet.Closed P S) {c : PCfg St I} (hc : S c)
    {i : I} (hm : i ∈ c.pend) : S ⟨(P.step i c.st).1, c.pend.erase i⟩ :=
  hS c _ hc (.single (.apply c i hm))

/-- The pending list reordered. -/
theorem PSet.Closed.perm {S : PSet St I} (hS : PSet.Closed P S) {c : PCfg St I} (hc : S c)
    {p : List I} (hp : p.Perm c.pend) : S ⟨c.st, p⟩ :=
  hS c _ hc (.single (.perm c p hp))

end linkv
end EtcdGrove
end Perennial
