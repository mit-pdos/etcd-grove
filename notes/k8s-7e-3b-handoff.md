# k8s 7e-3b handoff (2026-11-08, branch `k8s-7e`, fourth agent: 7e-3b complete)

State for the next agent; read `notes/k8s-7e-3b-plan.md` first. Scratch: `/shared/tmp/k8s-7e-3b/`
(`gen.py` writes a spec/proof skeleton pair in the driver's layout; `b*.py` are the batches used).

## Done

- (a) the object layer (`fd01648df2`, `c6bb6a70c4`); option (B), `Output.Items` an encoded string
  (`90b6252aa5`); the non-list model functions (`7f2ad6c9b5`).
- `objOf` spec/proof.
- **7f's record fields (81, 2026-11-08), `778fd04ed7`**: `Input` gains `WKey`, `SendInit`,
  `Bookmarks`, `Behavior`, `Skip`; `Output` gains `WEvents` (string), `WFailed`; Go `outEqual`
  compares them (so `outEqual.spec`'s `decide (a = b)` stays true). Only the record fields: 7f's
  `watch.go`, `KWatch`, `step`'s `watchOk`, `Gen`/`Apply`/`Check` changes and `lintest.RunLin2`
  stay 7f's. Re-translated, Go tests pass (86s). `KModel` decEqs, `errOutL`/`objOutL`, `listOutL`,
  `Input/Output_intoVal_inj`, `outEqual` (its `Output_eq_iff` was stale: now all 17 fields).
- **The list model, `KList.lean`** (new): selectors (`labelSelL`, `fieldSelForL`, `objField`,
  `selOkL`, `predEmptyL`), `pastReadL`, `matchOptL`, `trimSufL`, `keyInScopeL`, `scopeL`, `limitN`,
  `listLoopL` (= `ListModel.loop` on the items in scope), `encL` (an `opaque` def, no axiom),
  `encOkL`, `listOutL`, `predV`/`listOptsV` (the Go values `predicate`/`listOptions` return),
  **`HSt`** (store + history), `histAtL`, `advanceL`, `listStL`, **`mlistL`**, **`kstepL`** (list:
  `mlistL`, else `mstepL` advanced), **`kSpec h0 := ⟨h0, kstepL, isWriteL⟩`** (moved here from
  `KModel`), `kstepL_write`, `histAtL_*` lemmas.
- **`KSteps`**: `GCfg := PCfg HSt Input`; `stepL`/`succAt` on `kstepL`; `Bounded n g` now also
  bounds `hist + pend < n` and says pending inputs are writes (closure steps them with `mstep`);
  `kstepL_length`; `bounded_gInit` at `items + hist + 1`. Builds.
- **`MDefs`**: `histOwnR`/`histOwn` (persistent; nodes `↦□`, `n' = W64 len`), `histOwn_nil`,
  `histOwn_snoc`, `storeOwn_agree`, `histOwn_agree`; `cfgOwn c g := storeOwn ∗ histOwn ∗ pend ↦*□ ∗
  ⌜hist.length < 2^64⌝`; `stRepB`/`k8setcd3S` on `HSt`.
- Proved (spec + proof, no sorry): `pastRead`, `keyInScope` (hyp: `strings.TrimSuffix.spec`, an
  existing axiom), `matchOpt`, `fieldSelFor`, `histLen`, `appendHist`, `advance` (premise
  `hist+1 < 2^64`), `histAt` (premise `len < 2^64`), `histOf`, `histEqual`, `configEqual` (now
  with `histEqual`), `encodeItems` (slice read-only), `outEqual`.
- Also proved: `predicate`, `listOptions` (`predV`/`listOptsV` in `KList`). Built (targeted lake
  build, 2026-11-08): the two hypothesis specs
  `Spec/k8s_io/apiserver/pkg/storage/{SelectionPredicate__Matches,PrepareContinueToken}.lean`
  (driver-specialized; for 7e-2's Draft) and `mlist`'s spec; `mlist`'s proof is a `sorry`
  skeleton with its hypotheses listed.
- Not yet redone (break on the new `cfgOwn`/`GCfg`, expected): `step`, `closure`, `Model`, maybe
  `addConfig`; and the 7e-4 files (`Refine`, `Inv*`, `Model.lean`, `Seed`, `Apply`, `Check`, ...).

## The `k8setcd3S` change (Q7e-3b-1), old -> new (for the report to 81)

- `M := pM (kSpec g0) decOp`, `g0 : GSt`, `kSpec` of `mstepL` -> `g0 : HSt` (store + history),
  `kSpec` of `kstepL` (lists answered by `mlistL`, writes advance the history).
- `rep k := stRepB g0 (k + g0.items.length + 1)` -> `stRepB g0 (k + g0.st.items.length +
  g0.hist.length + 1)`; `stRepB`'s configurations own their history read-only (`cfgOwn`).
- `ioOk` unchanged (option (B): outputs stay plain values; no points-to in the I/O fact).

## Done by the fourth agent (2026-11-08): 7e-3b complete, no `sorry` in its files

- **`mlist` proved** (`769997e1b8`, `6365ede8d8`): `wp_join` on the past-read `if` (the store read
  `storeOwn s (listStL x g.st req)`), the range loop with invariant "the state is `listLoopL x
  (take j items)`" (`KList`: `scopeL_take_succ`, `listLoopL_take_succ`, `listLoopL_le`), the
  `Matches`/`PrepareKey`/`PrepareContinueToken` hypotheses, `encodeItems` on the persisted items
  slice. Its spec now has **no premise** (`cfgOwn c g` only): the loop's `int64` counters stay
  below the store slice's length. (A kernel error came from `generalize` with abstracted proofs:
  use `obtain ⟨S, hS⟩ : ∃ S, e = S := ⟨_, rfl⟩; rw [hS]` instead.)
- **`step`** (`6365ede8d8`): a list answers `mlist` (and returns `[c]`); any other call `mstep` then
  `advance(c, st, c.pend)`. Premise gains `g.st.hist.length + 1 < 2^64` (advance's); callees gain
  `mlist`, `advance`.
- **`closure`** (`6365ede8d8`): the inner loop's `advance(c, st, removeAt(c.pend, i))`; a pending
  input is a write (`Bounded`), so `succAt` is `kstepL_write`'s. Callee gains `advance`; spec's
  `st0 : HSt`.
- **`Model`** (`Model(st0, h0)`): spec takes `storeOwn s0 g0.st ∗ hsl ↦*□ hs ∗ [∗list] storeOwn
  hs g0.hist` and `g0.st.items.length + g0.hist.length < 2^60` (`g0 : HSt`); `Init` calls
  `histOf(h0)` (read-only `h0`: Init runs on every call). Callee gains `histOf`. `addConfig`
  builds unchanged.
- `inputEqual`, `storeEqual` (`8f8dddce2b`): their `_eq_iff` lemmas on the new records (Input 32
  fields, Obj 8 with `Annotated`).
- Optional: `fieldSel.{Empty,RequiresExactMatch}`, `labelSel.{Empty,RequiresExactMatch}` specs and
  proofs (`d9e48963d1`).
- Verified: targeted `lake build` of every function proof module of the driver (64G cap): only
  `Refine` (7e-4) and `workloadKeys` fail (below), plus the now-fixed `inputEqual`/`storeEqual`.

## Left (not 7e-3b's, or optional)

- `workloadKeys`: the workload keys are now `ns-1/pod-1`, ... (7e-0); `wksD` and `genFrom`'s
  proof (which uses `wksD`, `% 3`) go with the generator's redo (`genList`/`genFrom`, the Scope
  counts them with the new functions; 7e-4 if not done before).
- `fieldSel.Matches`/`labelSel.Matches` and `getAttrs`: `fields.Set`/`labels.Set` are names-only
  in the translation (`Code/k8s_io/apimachinery/pkg/{fields,labels}.toml`), so `Get`/`Has` need
  specs at the trust boundary (hypotheses or axioms): with the `Matches` hypothesis, for 7e-2's
  Draft. The `transform`/`String`/`Requirements`/`DeepCopySelector`/`Add` methods are not called
  by `SelectionPredicate.Matches`.
- 7e-4: `Link.lean` (the new callee hypotheses of `step`, `closure`, `Model`, `mlist`), `Refine`,
  `Inv*`, `Seed`, `Apply`, `Check`, ...; Model's callers must give `h0 ↦*□`.

## Next (the third agent's list, for the record)


1. `mlist`'s proof: `parseRV`, the too-large test, `pastRead`/`histAt` (from `cfgOwn`'s history),
   `predicate` (store into a local: `Matches` takes `pp ↦ predV x`), the range loop over
   `st.items` with invariant "state = `ListModel.loop` on `scopeL x (take j items)`" (`items`
   slice owned, appended: reversed `s.items`), `PrepareKey` (`prepareKeyM`), `PrepareContinueToken`,
   `encodeItems` (persist the items slice), the output literal vs `listOutL`. The spec's premise
   bounds counts (`< 2^62`); adjust if the loop needs others.
2. `step` (list branch: `outEqual`/`mlist`; others `advance`), `closure` (`advance` + `kstepL_write`
   via `Bounded`'s pending-writes fact), `Model` (`h0 []mstore` -> `histOf`; `Model.spec` takes
   the seeded history and `g0 : HSt`), `addConfig` (check it still builds).
3. Optional per the plan: the remaining selector methods and `getAttrs` (they are what proves the
   `Matches` hypothesis in 7e-2).
4. Report to 81 (7e-3b complete): the `k8setcd3S` change above, the two hypothesis statements,
   the 7f fields.
