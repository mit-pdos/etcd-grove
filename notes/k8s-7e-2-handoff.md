# k8s 7e-2 handoff (2026-11-10, branch `k8s-7e`, worktree `/shared/etcd-grove-k8s7d`)

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

## D1-D3, R1, item 2: done (third session, 2026-11-09; decisions in `questions.md`)
Built green, 8112 jobs (`/shared/tmp/k8s-7e-2/build6.log`; the list below plus every module that
names `rpctypesInit`). `etc/gen-init.py --check` passes.
- D1: rpctypes `ErrFutureRev`/`ErrCompacted` are `EtcdError` values (`etc/gen-init.py`, regenerated
  `rpctypes/Init.lean`, `rpctypesInit` in `cache/v3/Base.lean`); Go test
  `examples/k8s7e2attack/rpctypes_test.go` (`TestRpctypesErrTypes`, passes at the pin). `ListDefs`:
  `kClientErr` (client branch of `unkErr`; `kClientErr_unkErr`), used by `readErrIs`.
- D2: `AggrDefs.lean` (`freshAggr`, `aggrFactoryOk`); the factory specs return them (proved;
  `corruptObjErrAggregatorFactory.wp_proof` takes `wp_default`, `etc/link-lean-first-k8s-etcd3.txt` and
  `etcd3/Link.lean` regenerated); `isStore` ends with `storeListOk sp c` (`rseNilR`, `storePoolN`);
  `New.spec` gains `utf8Valid gr.Group' → utf8Valid gr.Resource' → threadBound GF ≤ 2 ^ 30 - 1 →`
  (the last for `init_RWMutex_threadPool`, reported to 81); `New` proved.
- D3: `NewResourceExpired.spec` post adds `st.Details' = null`.
- R1: `RecordEtcdRequest.spec`/`RecordDecodeError.spec` take `utf8Valid` premises; call sites discharge
  from `storeListOk`; `getCurrentState.spec` takes `utf8Valid verb`.
- `interpretListError` (pre `kClientErr`) and `store.listReadError` (premise `∃ k, prepareKeyM rp rp
  false = some k ∧ (pathPrefix ++ k).length ≤ opKeyMax`, for `GetCurrentResourceVersion`) proved. Not
  linked (no new trusted spec is linked yet; the last third links them).

## Eighth session (2026-11-10): the review's fixes, the trusted specs linked
Decisions: etcd-grove-81 (the coordinator's review of the trusted texts, results in its workflow
journal `wf_dac9ea87-502`, Go tests `/shared/tmp/k8s7e2-review/`). Done, one commit each:
- `IsTimeout`/`HasStatusCause` (refuted: typed-nil `*StatusError`, bare or `%w`-wrapped, panics in
  `Status()`): precondition `apiErrOk err` (`View.lean`: a `*StatusError` held read-only, or a
  `.plain` error; `apiErrAt_ok`); consumers `IsTooLargeResourceVersion` (from the view) and
  `createPods` (from `errIs`'s struct) discharge it; citation `errors.go:75-79`; Go test
  `TestTypedNilStatusError` gains the wrapped case.
- `Client.List.spec`, `store.getList.spec` (refuted: raw range below the prefix): premise
  `opts.Continue' = [] ∨ pfx <+: opts.Continue'`; `pagedChunks` discharges it (`pagesL_prefix` in
  `ListDefs`); `GetList` requires no continue key. `Client.GetAt`: the review holds, no change.
- `KindCompare`: an axiom (`Proof/reflect/KindCompare.lean`), Go test `TestKindIsUint`.
- `reflect.Type'`: `type_typed_pointsto` (an instance, `heapTypedPointsto` from the axiom
  `type_intoVal_inj : go.IntoValInj reflect.Type'`; depends on `hG`, `go_gctx`) and the axiom
  `type_into_val_typed`, both priority high over the generated `sorry`s (`Values.lean`). Value's
  instance untouched (premise-fixes-3 fixes it on lean; align Type' after merging).
- Docstrings: `Value.IsNil` (attack test), `json.Marshal` (JSONv2 at go1.27.3).
- Links: every 7e-2 trusted spec non-pending in `etc/link-lean-first-k8s-etcd3.txt` except
  `Client__List`/`Client__GetAt`; `etcd3/Link.lean` regenerated.
- **Next:** `#print axioms store.wp_GetList` (no `sorryAx`), `etc/tcb-report.py --check --update` and
  the collections, the full build (lock, 64G cap), STOP. After premise-fixes-3 lands: merge lean,
  RecordEtcdRequest's err precondition comes with it; align `Type'` with Value's pattern.

## Seventh session (2026-11-10): `GetList` proved
Rules: `/shared/tmp/coord-81/common-rules.md`. Decisions: `questions.md` (7e-2, seventh session).
- Done (no `sorry`; built capped, `/shared/tmp/k8s-7e-2/b21.log`, 7369 jobs):
  - `ForRange.lean`: `wp_forRange2` (local, proved; candidate Perennial addition in
    `notes/perennial-changes.md`), `wp_app_recV`.
  - `ListPages.lean` (pure): `scopeL`, `fromL`, `fromL_kp`, `fromL_next` (a page's last key and
    `"\x00"`), `goStringLt_append_zero`, `LAgree`/`chunkL_agree`, `kListL_agree`, `kListL_final`
    (the list at a `break`), `kListL_total`, `page0_full`, `pageKvsL_prefix`, `pageKvsL_more_ne`,
    `prepareKeyM_ne_nil`, `scopeL_prefix`, `chunkL_take_add`.
  - Forms (decided by the agent, `questions.md`): `pagesOk` stronger (a `false` yield gives
    `threadTok -∗ Φ #()`; the end premise only after a page without more, `pageMore`, new in
    `ListDefs`); `appendChunk.spec` post gains `lr = true → n = 0 → full st`;
    `Spec/.../store__GetList.lean` = Draft §2 + G1/G2 + `ctxNeverDone (ok ci)` + B5 (a).
  - `store.GetList.wp_proof` takes `[go.IsStrictlyComparable reflect.Kind.underlying w64]`
    (`reflect.Kind` is axiomatized in Perennial; decision needed before linking).
- GetList proof structure: `wp_post_named` names the code after the loop (`K`); `HkP` = `Fin ∧ Ret`
  (the post-loop continuation after a `break`, and after a `return`), carried in the loop invariant `J`
  (given to `pagesOk`), with `Tok` from `wp_forRange2`; the page yield names its post `Ψb`.
- Then (same session): the driver's `ListSpecD.lean` (`driverListSpec`, items as `itemRelD`, a
  pointwise filling of the Draft's `vs.map (objBody, rvString)`), `decoder.DecodeListItem`,
  `versioner.UpdateList` (specs + proofs), `ListContract.lean` (`driver_listContractOk'` from the
  reflect/GetItemsPtr specs as hypotheses, `driver_listContractOk`). Links: `etc/link-lean-first-
  k8s-etcd3.txt` gains the list path (new trusted specs, `Client__List`/`Client__GetAt` and
  `reflect_KindCompare` pending `?`, so hypotheses, no axiom linked); `etc/gen-link.py` gains
  `PER_FN_PENDING` (k8s-etcd3 only: a result takes only the pending hypotheses it reaches, so the
  compactor's results, used by `examples/k8s/compactor/MainLinked`, keep their statements; other
  modes regenerate identically). The driver's `Link.lean` regenerated (two new theorems; it is
  known broken until 7e-4, not built). `GetList`'s Kind premise is now an explicit hypothesis
  `reflect.KindCompare.spec` (`Spec/reflect/KindCompare.lean`, a Prop, pending).
  Interfaces: no `etc/api` module imports a changed module (`etc/importers.py`); not regenerated.
  Built capped: `b28.log` (7911 jobs, green; includes etcd3 `Link`, compactor `MainLinked`).
- **Finding (for 81):** `getNewItemFunc.wp_proof` (second session) depends on `sorryAx`: its code
  allocates a `reflect.Type'` cell, whose `TypedPointsto` is Goose's generated `sorry --
  axiomatized type` instance; `store.wp_GetList` in the etcd3 `Link` reaches it (checked with
  `#print axioms`; `GetList.wp_proof` itself and the other list-path results do not). Fix options:
  a trust-boundary `TypedPointsto reflect.Type'` axiom in `Proof/reflect/Values.lean` (as
  `value_typed_pointsto`), or a Perennial change.
- **Next:** 81's decisions (KindCompare, the `Type'` instance, the trusted texts' review); then link
  the trusted specs as axioms, `etc/tcb-baseline.txt` and collections (not done: STOP).
- Pitfalls: `iassert` does not exist (use `ihave H : (P) $$ [...]`); `swap`, `by_contra` absent;
  `cases h : x.f'` substitutes only where the goal already shows `x.f'`; a long proof needs
  `set_option maxHeartbeats 8000000 in`; `iunfold A B` takes one name (use `unfold A B` on the goal).

## Sixth session (2026-11-10, after B5 (a)): `pagedChunks` proved; next `GetList`
Read the Draft's B5 decision and `questions.md` (B5, and "Forms decided by the agent"; rules:
`/shared/tmp/coord-81/common-rules.md`, "Form-only changes").
- Done: `pagesL`, `chunkIs`, `pagesOk` in `ListDefs` (B5 (a); `pagesOk` a one-shot WP with
  `threadTok`, `Q`'s update and `P`'s persistent update as premises); `Spec/.../store__pagedChunks.lean`
  and its proof (no `sorry`; pure lemmas `pageKvsL_snd_le/fst_le/more/mem/key_nomore`, `limN_W64`,
  `pagesL_succ`, the loop invariant `pageInv`, all in the proof file). Built capped
  (`/shared/tmp/k8s-7e-2/b18.log`, 7354 jobs).
- **Next, in order:**
  1. `GetList` (Draft §2 with B5 (a): `P : KVState → KVState → IProp GF`, premise `Q R σ ∗ P σ σ' ⊢
     ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝`, update `□ ∀ R σ, □ Q R σ -∗ |==> …kvReadAu (P σ)`; plus
     `ctxNeverDone (ok ci)`, G1/G2). Its proof needs: `pagedChunks.spec` (premises: GetList's own;
     `listReadError`'s key premise from `storeListOk`'s `prepareKeyM rp rp false = some rp` and
     `prepareKeyM_prefix` on GetList's key: `(pathPrefix ++ rp).length ≤ (pathPrefix ++ k).length`);
     the range-over-func `for chunk, chunkErr := range chunks` is `func.forRange 2` (Perennial
     `Golang/Defn/Loop.lean`), which has **no WP lemma in Perennial**: unfold `func.forRange_unseal`
     (cells `state` (`go.int`) and `exit` (untyped `Alloc`)), or prove a local lemma
     `wp_forRange2` from `pagesOk`'s shape (record it in `notes/perennial-changes.md` as a candidate
     general lemma). `yieldOf 2` is the closure `λ "$k" "$v", step (λ <>, body "$k" "$v")`. Then
     instantiate `pagesOk`'s `J` with the loop state (items so far as `chunkL`'s state, `count`,
     `lastKey`, `hasMore`, `numFetched/numEvald`, `withRev`); compose pages into `kListL` (a pure
     lemma: the pages' `chunkL` over `pagesL` is `ListModel.loop` on the scope; `kListL_last`).
     Callees already proved: `shouldStream` (false: `rangeStreamOff`), `ValidateListOptions`,
     `getNewItemFunc`, `appendChunk`, `validateMinimumResourceVersion`, `PrepareContinueToken`,
     `finalizeList`, aggregator factory, `tracing.Start` (B2), the metrics, `GetItemsPtr`.
  2. The driver's `DecodeListItem`/`UpdateList`/`driver_listContractOk` (Draft §6).
  3. Links (`etc/gen-link.py` as in "Notes for the last third") and interfaces — STOP before linking
     the new trusted specs or touching `etc/tcb-baseline.txt`/collections.
- Patterns (pagedChunks): a closure's body: after `iapply HΦ; iunfold pagesOk; iintro …`, `wp_auto`
  enters it; callback WPs with a fixed post: `wp_bind (App (App (Val #y) _) _)` then `iapply (wp_wand
  (Φ := …)) $$ [..]`, and `iapply Hy $$ %a %b %c %(ch) [HJ] [] [Hkvs]` (goal patterns: the context
  goes to the last goal otherwise; `simp only [↓reduceIte]` before `iexact` on `J (if 0 = 0 …)`);
  `ipersist` on a fresh `revision` cell inside a WP; `generalize h : e = x` (no `at`) generalizes
  the Iris context too, and `rw` on the goal rewrites Iris hypotheses; no Mathlib (`set`, `swap`,
  `not_not` absent: `generalize`, reorder `by_cases`, `Decidable.not_not`); lean-check hides
  `trace` output; a WP post `{{ _, … }}` does not parse (`{{ v, … }}`); `do: v` on an unknown `v`
  needs `v.isPanic = false`: state yield posts as `∃ b : Bool, ⌜v = #b⌝ ∗ …`.

## Fifth session (2026-11-10): `getList` proved; stopped at B5
- `store.getList` proved (no `sorry`; both branches; `Client.List.spec`/`Client.GetAt.spec` premises
  of the proof only). Pure lemmas in `ListDefs`: `filter_key_eq_findKey` (on a key-sorted list,
  `filter (key = k)` is `(findKey k s).toList`) and `pageKvsL_key` (the non-recursive page is the
  key's key-value). Built capped (`/shared/tmp/k8s-7e-2/b15.log`, 7347 jobs, green).
- Stopped at **B5** (Draft, "Blocker found in the last third, after B1-B4"): a later page's
  `ErrFutureRev` makes `GetList.spec`/`pagesOk` unprovable from the Draft's premises. Not started:
  `pagedChunks`, `GetList`, the driver's `DecodeListItem`/`UpdateList`/`driver_listContractOk`,
  links, interfaces.
- `getList` patterns: the interface call `s.client.Kubernetes.List` resolves with `rw
  [method_unfold (t := go.GoType.PointerType kubernetes.Client.ty) (m := go!"List")]; wp_call`; the
  `[]*KeyValue{…}` literal with `wp_apply wp_slice_literal`; the empty literal's `List.replicate
  (go.arrayLiteralSize []).toNat _` is `[]` by `rfl`; Iris lemmas `BigSepL2.bigSepL2_nil`/`_cons`
  (`.2` with `iapply`), `iempintro`; `generalize e = x` (no `at`) generalizes the Iris context too.

## Last third, after 81's decisions on B1-B4 (2026-11-09, same session)
Done: B2's Go test (`examples/k8s7e2attack/tracing_test.go`, passes: noop and SDK tracer); B2's
restatement (`ctxNeverDone` moved to `Proof/k8s_io/component_base/tracing/Defs.lean`;
`tracing.Start.spec` post gains `□ (ctxNeverDone (ok ci) -∗ ctxNeverDone (ok ci'))`; the three
callers' patterns gain `, -`); B1 (`storeListOk` ends with `⌜prepareKeyM rp rp false = some rp⌝`;
`New.spec` premise `prepareKeyM rp rp false = some rp`; the five `icases Hlst` patterns gain `, -`);
B3 (`kvWfHist`'s body is now a conjunction: decode, and `0 < uint.nat modRev ≤ r`). Built green
(`b12.log`, 7966 jobs; the driver's `Main*`/`Results` not built: they still pass New's old premises,
known broken until 7e-4 — add `hu1 hu2 htb` and `(by decide)` for the new premise there).
B4: `rangeErrSound` in `ListDefs`; hypothesis specs `Spec/go_etcd_io/etcd/client/v3/kubernetes/
Client__List.lean`, `Client__GetAt.lean` (no proof files: premises of `getList`'s proof only).
In progress: `store.getList` (spec written as Draft §3.5; proof started). Then `pagedChunks`,
`GetList` (premises: Draft §2 plus `ctxNeverDone (ok ci)`), driver side, links, interfaces.
Pure lemma needed for `getList`'s non-recursive branch: on a key-sorted list (`KVStore.kvs_sorted`),
`filter (key = kp)` is `(findKey kp kvs).toList`.

## Last third, fourth session (2026-11-09): stopped at blockers B1-B4
Read the Draft's "Forms proposed at Prove (last third)" and "Blockers found in the last third".
Proved (lean-check, then built of record capped: `/shared/tmp/k8s-7e-2/b9.log`, `b10.log`, green):
- `store.finalizeList` (spec + proof), `store.processListItem` (spec + proof; `ctxNeverDone` in
  `ListDefs`), `store.appendChunk` (spec + proof; `chunkL`, `decodedL`, `itemsOf`, `lastKeyIs` in
  `ListDefs`; pure lemmas `chunkAt_succ/full/step/length` in the proof file),
  `store.getResourceSizeEstimator` (spec + proof, new callee; the reader-pool borrow).
Not started: `getList` (needs B4's vocabulary), `pagedChunks` (needs `getList.spec`; can be done over
it as a hypothesis once B4 is settled), `GetList` (needs B1-B3), the driver's
`DecodeListItem`/`UpdateList`/`driver_listContractOk`, links and interfaces (nothing linked yet;
`etc/gen-link.py` not rerun).
Patterns learned: `wp_bind (App (Val wrapDefer) _); wp_apply wp_with_defer as %defer defer` for a
`defer`; nil-channel select: `wp_apply_core chan.wp_select_nonblocking_nil`, then
`chan.nilClausePre_recv Unit _ _ rfl`; `wp_bytes_to_string` for `[]byte` to a named string type;
inside `all_goals` after `case'` branches `word` can fail with "unknown free variable": unfold
`sint.nat`/`sint.Z` and use `omega`; `wp_if_destruct`'s hypothesis may come as `#(decide P) = #true`
in one branch copy (`go.intoVal_inj`); `{ (f x) with … }` needs the parentheses.

## Notes for the last third
- `GetList` must pass `listReadError`'s premise (the resource prefix's key): derive it from
  `prepareKeyM c.resourcePrefix key … = some k` or add it to `GetList.spec` (a form for 81).
- The list path's metrics take `utf8Valid` of `c.gr` from `storeListOk`; `getList` reads
  `getResourceSizeEstimator` under `collectorMux.RLock` with the pool in `storeListOk` (borrow with the
  thread token: `Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/Server__Get.lean`).
- `finalizeList`/`GetList` call the aggregator factory: `aggrFactoryOk`, `freshAggr`.
- Never run `etc/lean-check.py` on a file whose imports are stale after a low-level change: its `lake
  setup-file` rebuilds them without a memory cap. Build first with the capped `lake build`.

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
