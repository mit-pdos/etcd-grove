/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-3: the linearization model with foreign revisions (`pMF`)

The dist store's lintest ghost runs the semantic model of `SharedSem.lean` (`kSpec h0` with one more
silent step, the foreign revision) as a porcupine model: linkv's powerset construction (`PendModel.lean`'s
`pSeq`/`pM`) over `SReach` instead of `PReach`. A separate model, not a field of `linkv.PendSpec`: a field
would change `linkv.PSilent`, in which `realCheck`'s statement and the other linkv specs are written
(`notes/k8s-dist-k8-scope.md`, "Handoff K8-5").

- `fpost S x a`: the configurations reachable from `S`'s by silent steps, then `(x, a)` from a configuration
  that does not wrap (`PStep`), then silent steps again;
- `pSeqF h0`/`pMF h0 dec`: the model on abstract operations and on porcupine's, from `fInit h0`, the
  configurations silently reachable from `⟨h0, []⟩` (closed under silent steps, as every later state is);
- what the ghost's owner uses (`pSeqF_step_of`, the `FClosed` lemmas) and what the check's argument uses:
  **a run of `pMF` is a run of the semantic model** (`pMF_run`: `SRun h0 ⟨h0, []⟩ xs c'`, K8-8).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSem

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section go
variable [GooseExts]

/-- A silent step is a silent run. -/
theorem SReach.single {h0 : HSt} {c c' : GCfg} (h : SSilent h0 c c') : SReach h0 c c' :=
  .step h (.refl _)

/-- **Silent steps before a run**: they join the first operation's (or, with no operation, stay). -/
theorem SRun.reach_pre {h0 : HSt} {a b c : GCfg} {xs : List (Input × Output)}
    (hr : SReach h0 a b) (h : SRun h0 b xs c) : ∃ d, SRun h0 a xs d ∧ SReach h0 d c := by
  cases h with
  | nil => exact ⟨a, .nil a, hr⟩
  | cons h₁ hw hs hrest => exact ⟨_, .cons (hr.trans h₁) hw hs hrest, .refl _⟩

/-- The configurations after `(x, a)` from `S`. -/
def fpost (h0 : HSt) (S : linkv.PSet HSt Input) (x : Input) (a : linkv.Ans Output) :
    linkv.PSet HSt Input :=
  fun c' => ∃ c₀ c c₁, S c₀ ∧ SReach h0 c₀ c ∧ NoWrap c ∧ linkv.PStep (kSpec h0) c x a c₁ ∧
    SReach h0 c₁ c'

/-- The initial state: the configurations silently reachable from the start, nothing pending. -/
def fInit (h0 : HSt) : linkv.PSet HSt Input := fun c => SReach h0 ⟨h0, []⟩ c

open Classical in
/-- **The sequential model with foreign revisions** on abstract operations. -/
def pSeqF (h0 : HSt) : SeqModel (linkv.PSet HSt Input) (Input × linkv.Ans Output) where
  init := fInit h0
  step S io := if ∃ c, fpost h0 S io.1 io.2 c then some (fpost h0 S io.1 io.2) else none

/-- **The model with foreign revisions on porcupine's operations** `α`, through the decoder `dec`. -/
def pMF (h0 : HSt) {α : Type} (dec : α → Option (Input × linkv.Ans Output)) :
    SeqModel (linkv.PSet HSt Input) α where
  init := fInit h0
  step S a := (dec a).bind ((pSeqF h0).step S)

theorem pMF_step (h0 : HSt) {α : Type} (dec : α → Option (Input × linkv.Ans Output))
    (S : linkv.PSet HSt Input) (a : α) (x : Input) (o : linkv.Ans Output) (h : dec a = some (x, o)) :
    (pMF h0 dec).step S a = (pSeqF h0).step S (x, o) := by
  simp [pMF, h]

/-- **A step of the real configuration**: `c ∈ S`, silent steps to `c₁` (no wrap), `(x, a)` to `c₂`, silent
steps to `c'`; the model allows `(x, a)`, and its next state holds `c'`. -/
theorem pSeqF_step_of {h0 : HSt} {S : linkv.PSet HSt Input} {c c₁ c₂ c' : GCfg} {x : Input}
    {a : linkv.Ans Output} (hS : S c) (hr : SReach h0 c c₁) (hw : NoWrap c₁)
    (h : linkv.PStep (kSpec h0) c₁ x a c₂) (hr' : SReach h0 c₂ c') :
    ∃ S', (pSeqF h0).step S (x, a) = some S' ∧ S' c' := by
  have hp : fpost h0 S x a c' := ⟨c, c₁, c₂, hS, hr, hw, h, hr'⟩
  refine ⟨fpost h0 S x a, ?_, hp⟩
  simp only [pSeqF]
  split
  · rfl
  · next hn => exact absurd ⟨c', hp⟩ hn

/-- What the model's next state is, when it allows `(x, a)`. -/
theorem pSeqF_step_some {h0 : HSt} {S S' : linkv.PSet HSt Input} {x : Input} {a : linkv.Ans Output}
    (h : (pSeqF h0).step S (x, a) = some S') : S' = fpost h0 S x a := by
  simp only [pSeqF] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A state is closed under silent steps (late effects and foreign revisions). -/
def FClosed (h0 : HSt) (S : linkv.PSet HSt Input) : Prop :=
  ∀ c c', S c → SReach h0 c c' → S c'

theorem fInit_closed (h0 : HSt) : FClosed h0 (fInit h0) :=
  fun _ _ hc hr => SReach.trans hc hr

theorem fpost_closed (h0 : HSt) (S : linkv.PSet HSt Input) (x : Input) (a : linkv.Ans Output) :
    FClosed h0 (fpost h0 S x a) := by
  rintro c c' ⟨c₀, c₂, c₁, h0', hr0, hw, hs, hr1⟩ h
  exact ⟨c₀, c₂, c₁, h0', hr0, hw, hs, hr1.trans h⟩

/-- Every state the model reaches is closed. -/
theorem pSeqF_step_closed {h0 : HSt} {S S' : linkv.PSet HSt Input} {x : Input} {a : linkv.Ans Output}
    (h : (pSeqF h0).step S (x, a) = some S') : FClosed h0 S' := by
  rw [pSeqF_step_some h]; exact fpost_closed h0 S x a

/-- A foreign revision, in a closed state. -/
theorem FClosed.foreign {h0 : HSt} {S : linkv.PSet HSt Input} (hS : FClosed h0 S) {c : GCfg} (hc : S c)
    (hw : NoWrap c) : S ⟨foreignL c.st, c.pend⟩ :=
  hS c _ hc (.single (.foreign c hw))

/-- A late effect or a reordering of the pending writes, in a closed state. -/
theorem FClosed.pend {h0 : HSt} {S : linkv.PSet HSt Input} (hS : FClosed h0 S) {c c' : GCfg} (hc : S c)
    (hw : NoWrap c) (h : linkv.PSilent (kSpec h0) c c') : S c' :=
  hS c _ hc (.single (.pend hw h))

/-- **A run of the abstract model is a run of the semantic model**, up to silent steps at its end. -/
theorem pSeqF_run (h0 : HSt) :
    ∀ (xs : List (Input × Output)) (S S' : linkv.PSet HSt Input),
      run (pSeqF h0) S (xs.map fun p => (p.1, ansOf p.2)) = some S' →
      ∀ c', S' c' → ∃ c d, S c ∧ SRun h0 c xs d ∧ SReach h0 d c'
  | [], S, S', h, c', hc' => by
    simp only [List.map_nil, run, Option.some.injEq] at h
    subst h
    exact ⟨c', c', hc', .nil c', .refl _⟩
  | (x, y) :: xs, S, S', h, c', hc' => by
    simp only [List.map_cons, run] at h
    split at h
    · next S1 hs =>
      obtain ⟨c1, d, hc1, hrun, hd⟩ := pSeqF_run h0 xs S1 S' h c' hc'
      rw [pSeqF_step_some hs] at hc1
      obtain ⟨c₀, c, c₁, hS0, hr0, hw, hst, hr1⟩ := hc1
      obtain ⟨d', hrun', hd'⟩ := SRun.reach_pre hr1 hrun
      exact ⟨c₀, d', hS0, .cons hr0 hw hst hrun', hd'.trans hd⟩
    · cases h

/-- A state the model reaches from a nonempty one is nonempty. -/
theorem pSeqF_run_nonempty (h0 : HSt) :
    ∀ (l : List (Input × linkv.Ans Output)) (S S' : linkv.PSet HSt Input), (∃ c, S c) →
      run (pSeqF h0) S l = some S' → ∃ c, S' c
  | [], S, S', hS, h => by
    simp only [run, Option.some.injEq] at h
    subst h; exact hS
  | io :: l, S, S', _, h => by
    simp only [run] at h
    split at h
    · next S1 hs =>
      refine pSeqF_run_nonempty h0 l S1 S' ?_ h
      simp only [pSeqF] at hs
      split at hs
      · next hc => cases hs; exact hc
      · cases hs
    · cases h

/-- **A run of `pMF` is a run of the semantic model from the start** (K8-8: what `searchRun_accepts` takes):
the operations `l` decode to `xs`, each answer the output's `ansOf`. -/
theorem pMF_run (h0 : HSt) {α : Type} (dec : α → Option (Input × linkv.Ans Output)) (l : List α)
    (xs : List (Input × Output)) (hdec : List.Forall₂ (fun a p => dec a = some (p.1, ansOf p.2)) l xs)
    {S' : linkv.PSet HSt Input} (h : run (pMF h0 dec) (pMF h0 dec).init l = some S') :
    ∃ c', SRun h0 ⟨h0, []⟩ xs c' := by
  have hr : ∀ (S : linkv.PSet HSt Input) (l : List α) (xs : List (Input × Output)),
      List.Forall₂ (fun a p => dec a = some (p.1, ansOf p.2)) l xs →
      run (pMF h0 dec) S l = run (pSeqF h0) S (xs.map fun p => (p.1, ansOf p.2)) := by
    intro S l xs hf
    induction hf generalizing S with
    | nil => rfl
    | cons ha _ ih =>
      simp only [List.map_cons, run]
      rw [pMF_step h0 dec _ _ _ _ ha]
      split <;> simp_all
  rw [hr _ l xs hdec] at h
  obtain ⟨c', hc'⟩ := pSeqF_run_nonempty h0 _ _ _ ⟨⟨h0, []⟩, .refl _⟩ h
  obtain ⟨c, d, hc, hrun, -⟩ := pSeqF_run h0 xs _ _ h c' hc'
  obtain ⟨d', hrun', -⟩ := SRun.reach_pre hc hrun
  exact ⟨d', hrun'⟩

end go

end k8s_dist
end EtcdGrove
end Perennial
