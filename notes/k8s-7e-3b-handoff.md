# k8s 7e-3b handoff (2026-11-08, branch `k8s-7e`, third agent)

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
- Written, being checked when the context ran out: `predicate`, `listOptions` (proofs short;
  check the value `predV` matches what `wp_auto` computes: interface conversion of the selector
  struct values and `functions getAttrs []`), the two hypothesis specs
  `Spec/k8s_io/apiserver/pkg/storage/{SelectionPredicate__Matches,PrepareContinueToken}.lean`
  (driver-specialized; for 7e-2's Draft), and `mlist`'s spec (proof: `sorry`).

## The `k8setcd3S` change (Q7e-3b-1), old -> new (for the report to 81)

- `M := pM (kSpec g0) decOp`, `g0 : GSt`, `kSpec` of `mstepL` -> `g0 : HSt` (store + history),
  `kSpec` of `kstepL` (lists answered by `mlistL`, writes advance the history).
- `rep k := stRepB g0 (k + g0.items.length + 1)` -> `stRepB g0 (k + g0.st.items.length +
  g0.hist.length + 1)`; `stRepB`'s configurations own their history read-only (`cfgOwn`).
- `ioOk` unchanged (option (B): outputs stay plain values; no points-to in the I/O fact).

## Next, in order

1. Finish checking `predicate`, `listOptions`, the hypothesis specs, `mlist.spec` (build them).
2. `mlist`'s proof: `parseRV`, the too-large test, `pastRead`/`histAt` (from `cfgOwn`'s history),
   `predicate` (store into a local: `Matches` takes `pp ↦ predV x`), the range loop over
   `st.items` with invariant "state = `ListModel.loop` on `scopeL x (take j items)`" (`items`
   slice owned, appended: reversed `s.items`), `PrepareKey` (`prepareKeyM`), `PrepareContinueToken`,
   `encodeItems` (persist the items slice), the output literal vs `listOutL`. The spec's premise
   bounds counts (`< 2^62`); adjust if the loop needs others.
3. `step` (list branch: `outEqual`/`mlist`; others `advance`), `closure` (`advance` + `kstepL_write`
   via `Bounded`'s pending-writes fact), `Model` (`h0 []mstore` -> `histOf`; `Model.spec` takes
   the seeded history and `g0 : HSt`), `addConfig` (check it still builds).
4. Optional per the plan: the remaining selector methods and `getAttrs` (they are what proves the
   `Matches` hypothesis in 7e-2).
5. Report to 81 (7e-3b complete): the `k8setcd3S` change above, the two hypothesis statements,
   the 7f fields.
