# porcupine PR #46's `CheckOperations`: the closest true spec, premises in the precondition

**Kind**: a public result whose old statement (porcupine v1.3.1's `b = true ↔ Linearizable`) is
false of new code (anishathalye/porcupine#46, a DAG search over per-client chains); the spec is
the closest true one, with the old statement a corollary. `PorcupineDag/Spec/github_com/
anishathalye/porcupine/CheckOperations.lean`; the plans and their reviews in
`notes/porcupine-dag-plan.md`.

## First version (after three spec reviews)

```lean
∀ σ S m sl ops dq,
  HistOk ops → ClientsOk ops →
  {{ isPkgInit porcupine ∗ context.isClosedchanInit ∗
     isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops }}
    CheckOperations m sl
  {{ (b : Bool), RET #b;
     ⌜b = true ↔ LinearizableCO S.M (histOf ops) (clientOrder ops)⌝ ∗ sl ↦*{dq} ops }}
```

- `LinearizableCO`: linearizable by an order respecting real time *and* each client's listed
  order; what the PR's search decides (it implies `Linearizable`).
- `ClientsOk = ClientIdsOk ∧ MonoReturns`: client ids non-negative and within gc's `maxAlloc`
  (Go panics otherwise, Perennial does not model the limit), and returns non-decreasing along each
  client (the PR is unsound without it).
- Corollaries in `Results.lean`: `spec_seq` (v1.3.1's exact post under sequential clients) and
  `spec_sound` (`true → Linearizable` under `ClientsOk` alone).

## Critique 1 (the user, 2026-11-03)

"Put the preconditions inside the precondition for the Hoare triple rather than as pure
implications." Changed: `HistOk ops → ClientsOk ops →` became `⌜HistOk ops⌝ ∗ ⌜ClientsOk ops⌝` at
the end of the precondition, in this spec, its siblings (`CheckOperationsTimeout`/`Verbose`,
`checkOperations`), the corollaries, and v1.3.1's same four specs on the main tree, so both ports
read alike. Principle: "Pure premises go in the precondition".

## Approved

```lean
∀ σ S m sl ops dq,
  {{ isPkgInit porcupine ∗ context.isClosedchanInit ∗
     isModel S m ∗ sl ↦*{dq} ops ∗ opsIoOk S ops ∗ ⌜HistOk ops⌝ ∗ ⌜ClientsOk ops⌝ }}
    CheckOperations m sl
  {{ (b : Bool), RET #b;
     ⌜b = true ↔ LinearizableCO S.M (histOf ops) (clientOrder ops)⌝ ∗ sl ↦*{dq} ops }}
```

The user approved it by asking for the merge into `lean` (2026-11-03).
