# k8s etcd3 stage 7e-2: attack on the Draft's trusted statements (2026-11-09, for etcd-grove-81)

The `axiom` skill's method on the trusted statements of `notes/k8s-7e-2-draft.md` §5 (14 new, 3
restated, the gate) and on the §6-7 hypotheses a closed theorem would rest on, before any Lean. For
each: can a Go program that uses the library as k8s's apiserver etcd3 store does panic, or get a
result the statement excludes, while its triple follows from the statement?

Evidence: `examples/k8s7e2attack/attack_test.go` (own `go.mod`: the driver's at
`examples/k8s/etcd3/go.mod`, so apimachinery `0b7d352f711c`, apiserver `9c4ec15b8038`,
component-base `cd2c1afd246a`, and the driver's `Obj`/`ObjList` imported, not copied). Run:
`GOWORK=off GOTOOLCHAIN=go1.27.3 go test -count=1 -v ./...` under `systemd-run -p MemoryMax=32G`:
15 tests, all pass (each one asserts the outcome named below, panics included). No Lean counterexample
was written: the one refutation (T8) is the same class as a documented Perennial limitation, and
the metrics finding (T16-T17) needs `metrics.Register`, which has no spec here (see each).

## Verdicts

| # | Statement (Draft §) | Verdict | Test |
|---|---|---|---|
| T1 | `apierrors.IsTimeout` (§5.1, new) | **needs a definition**: `leafErrTy` must exclude `As(any) bool` and `Unwrap() []error` (and `Unwrap() error`); Lean `knownReasons` must not contain `""` | `TestStatusView`, `TestPlainView`, `TestLeafMustExcludeAsAndUnwrapSlice`, `TestTypedNilStatusError`, `TestTooLargeAndExpired` |
| T2 | `apierrors.HasStatusCause` (§5.1, restated) | same as T1 (the same `.plain` view) | same |
| T3 | `reflect.Value.Kind` | holds | `TestKindLenCapIsNil` |
| T4-5 | `reflect.Value.Len`, `Cap` | hold | `TestKindLenCapIsNil` |
| T6 | `reflect.Value.IsNil` ("some bool") | holds (sound), **too weak for `finalizeList`**: strengthen | `TestKindLenCapIsNil` |
| T7 | `reflect.Type.Elem` | holds | `TestKindLenCapIsNil` |
| T8 | `reflect.MakeSlice` (at `Obj`) | **false as stated** (huge `m` panics) | `TestMakeSliceHugeCapPanics`, `TestMakeSlice` |
| T9 | `reflect.Copy` | holds | `TestCopy` |
| T10 | `reflect.Append` | holds (as Perennial's `append`, incl. its allocation limitation) | `TestAppendSet` |
| T11 | `reflect.Value.Set` (restated: slice case) | holds | `TestKindLenCapIsNil`, `TestAppendSet` |
| T12 | `reflect.ValueOf` (restated: `Elem`) | holds | `TestAppendSet` |
| T13 | `meta.GetItemsPtr` (§5.3) | holds | `TestGetItemsPtr` |
| T14 | `json.Marshal` of the token (§5.4) | holds (tokJson is not injective: no property may claim it) | `TestMarshalToken` |
| T15 | `RawURLEncoding_init`, `base64Init` restated | holds | `TestRawURLEncoding`, `TestMarshalToken` |
| T16 | `metrics.RecordStorageListMetrics` (§5.5) | **false under k8s's use** (registered metrics): negative counts and non-UTF-8 labels panic; needs premises | `TestMetricsUnregistered`, `TestMetricsRegistered` |
| T17 | `metrics.RecordListLatency` | **false under k8s's use**: non-UTF-8 labels panic; needs a premise | same |
| T18 | the gate (§5.6, B5's text) | holds per B5 (`/shared/tmp/sweep-repairs-1/b5-r1.md`, its 3 tests); not re-attacked, reused unchanged | (B5's) |
| H1 | `listContractOk` / `ListSpec` (§6) | follows from T3-T13 for the driver; **`ListSpec` lacks a length law**; the MakeSlice clauses inherit T8's fix | — |
| H2 | `Client.List.spec` as consumed (§7) | consistent with `client.go:59-74`; **`getList.spec` cannot meet its `Continue` premise** | — |
| H3 | `Client.Get.spec` at a revision (§7) | consistent with `client.go:47-57` | — |
| R1 | (existing) `metrics.RecordEtcdRequest`, `metrics.RecordDecodeError` | **same finding as T16-T17**: non-UTF-8 labels panic once registered | `TestMetricsRegistered` |

## T1-T2: `IsTimeout`, `HasStatusCause`

Go: `errors.go:96-109` (`StatusCause`: `err.(APIStatus)`, else `errors.As(err, &status)`, then
`Status().Details`), `:689-698` and `:817-822` (`reasonAndCodeForError`).

- `.status` view: 990 statuses (19 known reasons, `""`, unknown ones; codes incl. 504, negative,
  extremes; nil/empty/duplicate details; 4 cause names) match `timeoutV`/`causeIn` exactly. Edge the
  Lean definition must get right: **`StatusReasonUnknown` (`""`) is not in `knownReasons`**
  (commented out at `errors.go:48`), so `Reason "" ∧ Code 504` is a timeout.
- A typed-nil `*StatusError` panics in both (nil dereference in `Status()`). Excluded: `.status`
  needs `l ↦□ _`, which gives `l ≠ null` (`typedPointsto_not_null`); `.plain` needs `t ∉ APIStatus`.
- **The `.plain` view as the Draft describes it** ("a leaf whose dynamic type has no `Status()`
  method; `errors.As` finds none") leaves `leafErrTy` undefined. `errors.As` also calls an
  `As(any) bool` method and follows `Unwrap() []error`: `asErr` (a leaf without `Unwrap`, outside
  `APIStatus`, with an `As` method) and `joinErr` (`Unwrap() []error`) make `IsTimeout`,
  `HasStatusCause` and `IsTooLargeResourceVersion` return `true`. If `leafErrTy t` were "no
  `Unwrap() error`", the statement's `.plain => false` would be refuted by either.
- Wrapped errors (`%w`) are in neither view (the statement says nothing of them): fine.

**Required definition**: `leafErrTy t` := the method set of `t` contains none of `Unwrap() error`,
`Unwrap() []error`, `As(any) bool` (and, already stated, `t ∉ APIStatus`'s type set); with
`knownReasons` the 19 reasons of `errors.go:49-67`, `""` excluded. With these, T1-T2 hold.

## T6: `IsNil` is too weak (provability, not soundness)

The Draft says "any `IsNil` answer leaves the same items" (§3.6). False: when `IsNil` is `true`,
`finalizeList` runs `v.Set(reflect.MakeSlice(v.Type(), 0, 0))`, which empties the list
(`TestKindLenCapIsNil`); with a "some bool" post the `true` branch must prove `listAt lx os ...`
from `itemsAt s' []`, impossible for `os ≠ []`. Go: `IsNil` of a slice is `Data == nil`, which
implies `Len == 0` (checked on nil, `{}`, `make(0,5)`, `make(3,7)`).

**Proposed post**: `{{ (b : Bool), RET #b; ⌜b = true → uint.Z s.len = 0⌝ ∗ vp ↦{dq} v ∗ p ↦{dq'} s }}`
(true: `Data == nil` only for a nil slice), plus H1's length law to get `os = []`.

## T8: `MakeSlice` — refuted as stated

Claim: `0 ≤ n ≤ m` suffices for no panic. Go (`reflect/value.go` `MakeSlice` →
`runtime.unsafe_NewArray`): if `m·sizeof(Obj) > maxAlloc` (2^48 on linux/amd64) it panics
`runtime: allocation size out of range`, before allocating. `sizeof(Obj) = 112`, so the threshold is
`m > 2513169434916`. Test output:

```
MakeSlice(rt, 0, 4611686018427387904) panics: runtime: allocation size out of range
MakeSlice(rt, 0, 9223372036854775807) panics: runtime: allocation size out of range
MakeSlice(rt, 0, 2513169434917) panics: runtime: allocation size out of range
make([]Obj, 0, 1<<62) panics too: runtime error: makeslice: cap out of range
```

The program `reflect.MakeSlice(reflect.TypeOf([]Obj(nil)), 0, 1<<62)` has a triple by one
`wp_apply` of the axiom. Same class as Perennial's documented unsoundness (`docs/KNOWN_LIMITATIONS.md`,
"No limit on allocation size (unsound)": `make`/`append` above `maxAlloc`), so the store's own
`make`/`append` share it; but this axiom is a new statement of this repository and need not repeat it.
The store never asks for such a slice (`growSlice`'s `max ≤ maxCapacity ∈ {len(kvs), 2048}`).

**Proposed text** (add one premise): `⌜reflType rt (SliceType Obj.ty) ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤
sint.Z m ∧ sint.Z m ≤ 2 ^ 41⌝` (2^41·112 < 2^48). Cost: `listContractOk'`'s two `MakeSlice` clauses
carry the bound, and `growSlice`'s proof needs `len(kvs) ≤ 2^41`, i.e. a bound on a response's
`Kvs` from 7e-1's `Client.List.spec` (a response is at most the client's max receive size, < 2^31
bytes) and on the non-recursive branch (1). Alternative: keep the text and cite
KNOWN_LIMITATIONS in the docstring as an accepted, documented gap. *Recommendation: the premise*
(the bound is one conjunct in 7e-1's post).

## T9-T13 (hold)

- `Copy`: dst lengths 0-3 vs src 0-3: returns `min`, writes `os.take |ds| ++ ds.drop |os|`, src
  unchanged.
- `Append`: from nil, `{}`, full, spare-capacity slices; the variable is unchanged until `Set`; the
  element is copied (mutating `*o` afterwards does not change the slice); with spare capacity the
  result shares the old backing array, which is why the spec consumes `s ↦* os ∗ ownSliceCap s`
  (correctly, as Perennial's `append`). `ValueOf(&o).Elem()` is settable; `ValueOf(nil *Obj).Elem()`
  is invalid (excluded by `p ≠ null`).
- `Set`'s slice case: `Set(MakeSlice(..))` and `Set(Append(..))` store the header into the field.
- `Kind` = `Slice`, `CanSet`/`CanAddr` true for `EnforcePtr(GetItemsPtr(l))` on nil/empty/non-empty
  items; `Type().Elem()` = `Obj`.
- `GetItemsPtr(&ObjList{..})` returns exactly `&l.Items` at type `*[]Obj`, `nil` error, for nil and
  non-nil items; a nil `*ObjList` errs (excluded by `pl ≠ null`).

## T14-T15 (hold)

`json.Marshal(&continueToken{"meta.k8s.io/v1", rv, k})` over keys `""`, `\x00`, invalid UTF-8,
`<>& `, quotes, 1 MiB, and rv ∈ {0, ±1, MinInt64, MaxInt64}: never an error, deterministic,
a fresh buffer (writing one result leaves the next unchanged), the token unchanged; and
`storage.EncodeContinue` equals `RawURLEncoding.EncodeToString(Marshal(..))` on all of them (§4.2's
`encL`). `"\xff"` and `"\xfe"` marshal to the same bytes (U+FFFD): `tokJson` is not injective in
the key, which the Draft already says no property relies on. `RawURLEncoding`: non-nil, no `=+/`,
deterministic, input unchanged, the variable unchanged.

## T16-T17 and R1: the metrics

Unregistered (the driver never calls `Register`), every call is a no-op: component-base's
`WithLabelValues` returns `noop` when `!IsCreated()` (`component-base/metrics/counter.go:198-201`).
But k8s's apiserver registers them (`apiserver/pkg/server/routes/metrics.go:53-60`:
`storagemetrics.Register()`, `etcd3metrics.Register()`), and then:

```
negative fetched                         panic: counter cannot decrease in value
negative evaluated                       panic: counter cannot decrease in value
negative returned                        panic: counter cannot decrease in value
invalid UTF-8 group                      panic: label value "\xff" is not valid UTF-8
invalid UTF-8 index                      panic: label value "\xff" is not valid UTF-8
latency invalid UTF-8                    panic: label value "\xff" is not valid UTF-8
RecordEtcdRequest invalid UTF-8 verb     panic: label value "\xff" is not valid UTF-8
RecordEtcdRequest invalid UTF-8 group    panic: label value "\xff" is not valid UTF-8
RecordDecodeError invalid UTF-8 group    panic: label value "\xff" is not valid UTF-8
```

(`storage/metrics/metrics.go:79-84`: `Counter.Add(float64(n))`; prometheus' `WithLabelValues`
validates UTF-8.) The statements quantify over all `w64` counts and all strings with no premise,
so "no panic on these label values" is false for k8s's (registered) use. No Lean counterexample
today: `Register` has no spec, so a program that reaches the registered state has no triple; the
statements are true of every program this repository can prove. Still a false trusted claim.

**Proposed text**:
- `RecordStorageListMetrics.spec`: add `0 ≤ sint.Z a → 0 ≤ sint.Z b → 0 ≤ sint.Z c' →
  utf8Valid gr.Group' → utf8Valid gr.Resource' → utf8Valid idx →`. The store passes `""` and
  `s.groupResource` (the driver's literal, ASCII: add `utf8Valid` of it to `isStore`/`StoreCfg`),
  and `numFetched`/`numEvald`/`v.Len()`, which the proof must show non-negative (no `int`
  overflow of the sums: a bound on the pages' total keys; `v.Len()` is a slice length).
- `RecordListLatency.spec`: add `utf8Valid gr.Group' → utf8Valid gr.Resource' →` (the streamed
  label is a literal; `Observe` of any float is fine).
- R1 (existing, outside 7e-2): `RecordEtcdRequest.spec` needs `utf8Valid verb`, `utf8Valid
  gr.Group'`, `utf8Valid gr.Resource'`; `RecordDecodeError.spec` the last two. Every caller passes
  literals and the store's `groupResource`.

Alternative (not recommended): keep them and state the environment assumption "the metrics are
not registered" in the docstrings; true for the driver, false for k8s.

## H1-H3: the hypotheses

- **H1** (`listContractOk`): the driver's instance follows from T3-T13 as the Draft says. Two gaps
  for the store's proofs (not trust): (i) `ListSpec` needs a length law, `itemsAt_len : itemsAt s os
  ⊢ ⌜uint.nat s.len = os.length⌝` (the driver's `s ↦* vs` gives it): `appendChunk`'s `v.Len() >=
  pred.Limit`, `GetList`'s `v.Len()` (paging break, metrics), `growSlice`'s `MakeSlice(.., v.Len(),
  ..)` (the contract's premise `sint.nat n = os.length`) and T6's `IsNil` branch all need it;
  (ii) the `MakeSlice` clauses take T8's bound.
- **H2** (`Client.List.spec`): `List` (`client.go:59-74`) reads `[rangeStart, GetPrefixRangeEnd(prefix))`
  with `WithLimit`/`WithRev`; `Count` is from `rangeStart` (as the Draft says); `Revision` is the
  header's (the store's current revision, `σ.rev`, also for past reads); `Kvs` is the decoded
  response's fresh slice (owned, requirement (a)). Gap: the spec requires
  `opts.Continue'.length ≤ opKeyMax`, but `store.getList.spec` (§3.5) has only `kp.length ≤
  opKeyMax`, and `pagedChunks` passes `lastKey ++ "\x00"`: `getList.spec` needs the premise
  `lo.Continue'.length ≤ opKeyMax`, and `pagedChunks` a bound `key.length < opKeyMax` on the
  stored keys (from `kvWf`, or etcd's request-size limit).
- **H3** (`Client.Get.spec`): `Get` (`client.go:47-57`) is `WithRev(rev)`, `WithLimit(1)`; `KV` is
  the one kv or nil, `Revision` the header's. Consistent.

## Recommended corrections (summary)

1. Define `leafErrTy t` as "no `Unwrap() error`, `Unwrap() []error` or `As(any) bool` method";
   `knownReasons` without `""` (T1-T2).
2. `MakeSlice`: add `sint.Z m ≤ 2 ^ 41`; carry it in `listContractOk'`; 7e-1's `Client.List` post
   bounds `len(Kvs)` (T8, refutation).
3. `IsNil` post `⌜b = true → uint.Z s.len = 0⌝`; `ListSpec.itemsAt_len` (T6, H1).
4. Metrics: non-negative counts and `utf8Valid` labels as premises of `RecordStorageListMetrics`
   and `RecordListLatency`, and of the existing `RecordEtcdRequest`/`RecordDecodeError` (T16-T17, R1).
5. `getList.spec`: `lo.Continue'.length ≤ opKeyMax`; a stored-key length bound for `pagedChunks` (H2).
