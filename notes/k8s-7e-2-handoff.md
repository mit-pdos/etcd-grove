# k8s 7e-2 handoff (2026-11-09, branch `k8s-7e`, worktree `/shared/etcd-grove-k8s7d`)

Read `notes/k8s-7e-2-draft.md` (with its "Corrections (2026-11-09)" and the two "Forms settled at
Prove" paragraphs) and `questions.md` (the 7e-2 sections). Scratch and logs:
`/shared/tmp/k8s-7e-2/` (`gen/*.py` generate spec/axiom/proof skeletons in the repo's layout).

## Done
- 7e-3c: `refine_list` (`examples/k8s/etcd3/RefineList.lean`), `ListDefs.lean`, `driverSpec_dec`.
- First third: the trusted texts of Draft §5 (reflect, `GetItemsPtr`, list metrics, `IsTimeout`,
  `HasStatusCause`, `json.Marshal`, base64 `rawUrlEnc`/`RawURLEncoding_init`), the error view
  (`Proof/k8s_io/apimachinery/pkg/api/errors/View.lean`), proved `NewTooLargeResourceVersionError`
  (post `tooLargeErrIs`), `IsTooLargeResourceVersion`, `ValidateListOptions`, `EncodeContinue`; `encL`
  a definition.
- Second third (part): `Set.Get/Has`; `SelDefs.lean`; the seven `SelectionPredicate` methods;
  the driver's `objLabels`, `getAttrs`, `labelSel/fieldSel.Matches` (`Sel.lean`); `PredOk.lean`
  (`predOk_driver`, `mlistMatches`, `mlistPCT`); generic `PrepareContinueToken`; `mlist` rewired.

## Done since (2026-11-09, second session)
- `rangeStreamOff` (`ListDefs.lean`), `shouldStream` (spec + proof).
- `getNewItemFunc` (spec + proof; `newItemOk` in `ListDefs`).
- `growSlice` (spec + proof) over `listContractOk'` (filled one clause per reflect call; the Draft's
  "Forms proposed at Prove (second third, part 2)").
- `ListDefs` vocabulary for the rest: `remIs`, `ListSpec` (+ `itemsAt_wf`), `listAtItems`, `listAt`,
  `listContractOk'`, `listContractOk`, `listIs`, `listErr`, `readErrIs`, `pageKvsL`, `listRespIs`.
- ETooLarge (#20): `respIs`'s `.tooLarge` case and `validateMinimumResourceVersion`'s post are
  `tooLargeErrIs`; its proof and `store.Get`'s follow.

## Blocked (decisions asked of etcd-grove-81, 2026-11-09)
- Item 2 (`interpretListError`, `listReadError`): `err == rpctypes.ErrCompacted` and
  `errors.Is(err, rpctypes.ErrFutureRev)` need the two globals' dynamic type (`EtcdError`), which
  `ErrCompacted_init`/`ErrFutureRev_init` and `rpctypesInit` do not state (their docstrings say it):
  a trust-base change. `errors.Is` also needs `statusErrOk err` (the client branch of `unkErr`).
- Item 5 (`isStore` #15, R1): `utf8Valid` of `gr` in `isStore` needs a `New.spec` premise; the
  aggregator factory needs the two factory specs' posts strengthened (`True` today); neither is in
  the Draft's §9 list of changed statements. R1 waits for it (its call sites discharge from `isStore`).

## Left of the second third, in order (original list)
1. `rangeStreamOff` (in `ListDefs.lean`, store part: `∃ g, globalAddr
   k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
   k8sfeature.featureOff g go!"EtcdRangeStream"`), then `shouldStream` (Draft §3.1). The gate's
   `Enabled` triple is `featureGateOk g` (`Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`), from
   `features`' package fact (`featuresInit`, `storage/etcd3/Base.lean`); `↦□` agreement ties its `g`
   to `rangeStreamOff`'s. `opts.Predicate.Empty()` needs the `opts` struct split (`iStructNamed`).
2. `interpretListError` then `listReadError` (§3.5): `readErrIs` (new, in `ListDefs`),
   `GetCurrentResourceVersion` (existing spec, trivial update), `NewTooLargeResourceVersionError`
   (now gives `tooLargeErrIs`), `apierrors.NewResourceExpired` (existing spec).
3. `getNewItemFunc` (§3.2: `Value.Type`, `Type.Elem`, `New`, `Value.Interface`, the `runtime.Object`
   assertion).
4. The list contract's reflect part `listContractOk'` (§6, in `etcd3/Contract.lean`) and `growSlice`
   (§3.3; the variadic `sizes` slice is a parameter).
5. `isStore` (#15): aggregator factory, `collectorMux` reader pool with `resourceSizeEstimator ↦
   null`, `utf8Valid` of `gr`; `New`'s proof; then R1 (`RecordEtcdRequest`/`RecordDecodeError` gain
   `utf8Valid` premises; every store method's call site discharges them from `isStore`).
6. ETooLarge (#20): `respIs`'s `.tooLarge` case and `validateMinimumResourceVersion`'s post become
   `tooLargeErrIs`; `store.Get`'s proof follows; the driver's `Calls.lean`/`errIs` is 7e-4's.
Then the last third (Draft §3.4-3.6, §2, §6 driver side, links): see the Draft's summary table.

## Pitfalls and patterns
- `rec` is a keyword: name Boolean binders `recur`.
- `||` under `open Iris` parses as disjoint union: write `Bool.or a b`.
- Iris hypotheses are not Lean hypotheses: `simp ... at H` fails; `rw [h]` on the goal rewrites
  the hypotheses inside the proof-mode context too (and must be redone if they later reappear).
- A field load of a struct points-to at a fraction other than `1` does not work: split first
  (`icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩`, `iStructNamed Hp`), recombine
  with `iapply typedPointsto_combine _ _ _ Hnn; simp only [TypedPointsto.typedPointstoDef]; iframe`.
- Persisting at the end of a function: `iapply wp_fupd` before the last `wp_auto`, then `ipersist`,
  `imodintro`.
- `wp_auto` stops at a method call on a value receiver of a translated type: use the callee spec,
  or `wp_method_call; wp_call` (e.g. a `labels.Set` method on `map.nil`).
- A spec with post `True`: `wp_apply` leaves `Φ ...` with nothing to introduce, so write no `as -`.
- `wp_apply spec $$ [Hm]` with a persistent `Hm` leaves the frame as a goal; use `[$Hm]`.
- `wp_if_destruct` needs a `decide`/Boolean variable: for `#opts.Recursive'` use `cases h :
  opts.Recursive'`; the first bullet is the condition's `true` case.
- String `len`: `github_com.mit_pdos.perennial.goose.model.strings.wp_string_len`; `fmt.Errorf`:
  `_root_.Perennial.fmt.wp_Errorf _ _ _ ArgsWf.nil` (with `ownSlice_nil` for `slice.nil`); map
  literals unfold to `wp_map_make1` plus `wp_mapInsert key_type m M k v`; `go.intoVal_inj` for
  `#a = #b`; `W8 0` in specs vs `0#8` in code: `rw [show (W8 0 : w8) = 0#8 from rfl]`.
- A `(predV x).GetAttrs'`/`(listOptsV x).Predicate'` projection is not unfolded by framing: convert
  with `ihave #H' : ... $$ []; · simp only [predV]; iexact H`.
- `driverSpec.objAt` vs `objAtD`: `rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl]`.
- `gen-init.py` with no flag regenerates (do not pass `--help`); edit its `SPECIAL`, never `Init.lean`.
- `questions.md` is git-ignored: decisions recorded there are not committed.
- The driver's `Refine.lean` and `Link.lean` are broken until 7e-4 (known); do not build them.

## Builds
Edit loop: `TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json python3
etc/lean-check.py -a -q $PWD/<file>`. Targeted build of record (as used, from the worktree):

```
cd /shared/etcd-grove-k8s7d && export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json \
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mlist \
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk \
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RefineList \
  Proof.k8s_io.apiserver.pkg.storage.PrepareContinueToken \
  Proof.k8s_io.apiserver.pkg.storage.EncodeContinue \
  Proof.k8s_io.apiserver.pkg.storage.ValidateListOptions \
  Proof.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion \
  Proof.k8s_io.apiserver.pkg.storage.etcd3.Link Proof.k8s_io.apiserver.pkg.storage.cacher.Link \
  Proof.encoding.base64.Init Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserAdd
```
Add each new module (its `Proof.*` name) and, for a changed statement, its importers
(`etc/importers.py --uses NAME FILE --leaves`). Last green: 7685 jobs, with `etcd3.shouldStream`, `etcd3.getNewItemFunc`, `etcd3.growSlice` added to the
list (`/shared/tmp/k8s-7e-2/build4.log`, 2026-11-09).
