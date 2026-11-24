# Proof craft: Perennial and Lean

Read Perennial's own docs first (`docs/PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`,
`IRIS_PROOF_MODE.md` in the dependency, `.lake/packages/perennial/`), and the specs of the
environment you call (`NET.md`): their headers say what they assume and give. What follows is what those do not say and what cost time.

## Records

A predicate takes its object's state as one record of pure values, holding only what the specs on it
need. In proofs:

- Keep a record a variable (`σ`, `ls`): do not destructure it with `intro ⟨a, b, c⟩`/`obtain`, and do
  not write a literal record where a variable will do. A projection of a literal record
  (`{ prev := p, … }.prev`) is an atom that `omega` and `rw` do not see through.
- For arithmetic use `word` (Perennial's), not `omega`: its preprocessing runs `simp`, which reduces
  projections of literal records and of record-building functions.
- Before `rw`/`subst`/`obtain ⟨rfl, …⟩` on a hypothesis that mentions such a projection,
  `simp only at h`.
- A function that builds a record from a Go value gets projection simp lemmas next to it (generate
  them for non-branching definitions).

## Large contexts

Never use a bare `iframe` (or any search over the whole context) when a goal or hypothesis holds a
`[∗list]` over `List.replicate n` with a large `n`: the unifier materializes the list (one such
search took 80 GB). Don't `unfold` a definition across a goal or context that size either; convert
locally through a lemma, and frame explicitly (`isplitl [H]`, `iexact`). The deployment's call
budgets and step bounds are such sizes.

## Definitional equality in the proof mode

`iframe`, `iexact` and `wp_apply`'s framing match hypotheses up to a shallow unfolding only. When a
general spec is used at a special mode (`specG false cmp` where the caller holds `inv` and the spec says
`invM false`), even if `invM false` is `inv` by `rfl`:

- first specialize the spec and rewrite it with the mode's `rfl` lemmas
  (`simp only [specG, invM_false, …] at h`), then apply it; or
- state the instance as its own one-line definition and give callers the rewritten form.

An argument whose expected type is an `if` on a literal Boolean may need
`(by simp only [Bool.false_eq_true, ↓reduceIte])` rather than `rfl`, when the other arguments are still
metavariables.

## Checking while editing

Use `etc/lean-check.py`, a Lean server kept running with the file open (an editor's behavior: after an
edit it re-elaborates from the first changed tactic). Each check returns at the first error in what changed. Loop: fix the
first error, check, fix the next. Ask for the proof state at a line (with the Iris context) instead of
inserting `trace_state`. For very long proofs: skip the kernel check and whole-proof linters during the
loop, and abstract each long `·` block into an auxiliary theorem so an edit re-checks only its block.
`lake build` stays the check of record.

What an edit costs: the tactics after the edit, plus the work done once per completed declaration
(instantiating the proof term, the kernel's check, linters), which grows with the proof's length. Keep
proofs under a few hundred lines; split long functions' proofs by their phases.

## Rebuild cost

Changing a statement or a definition rebuilds every importer; changing only a proof body does not
(Lake rebuilds an importer only when the imported module's public part changes). So: keep specs,
invariants and laws in small modules, split by phase or object and separate from the proofs, so a
change rebuilds little; edit proofs freely; batch statement changes.

Rebuild cost is not a criterion when repairing an invariant that keeps failing: choose the simpler
invariant, even if it changes widely imported definitions, and batch its rebuild into one round.

## Recurring patterns

- **Package initializers**: each Go package's initialization gives a persistent `isPkgInit` fact; a
  proof needs the facts of the packages it calls into. `etc/gen-init.py` writes the initializer
  theorems (`SETUP.md`); a package whose initializer is a declared premise is used through its
  `InitHyp` (`CHALLENGE.md`).
- **Goroutines**: a `go` statement's proof gives the spawned closure its resources; join through a
  channel or wait group whose invariant holds what comes back. Thread budgets are owned (`TRUST.md`).
- **Locks**: a lock invariant per mutex, stated over the protected fields' points-to's and the ghost
  state they mirror; assert it in tests at each unlock (`TESTING.md`).
- **Linearization points**: logically atomic specs (`PRINCIPLES.md`); the atomic update is committed
  inside the critical section, at the step the history records.
- **Prophecy variables** for operations whose linearization point is decided later (a read that returns
  a value fixed by a later event): the remote library's `Do` already has its own; one the system's
  code lacks comes from a prophecy patch (`CHALLENGE.md`).
