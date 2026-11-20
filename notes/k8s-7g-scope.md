# k8s etcd3 stage 7g, the maintainers' checker: Scope (2026-11-17, branch `k8s-7g`; to etcd-grove-03)

7g makes the closed theorems `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe`
say that **Kubernetes' own checker accepts the driver's histories**. That checker is the package
`k8s.io/apiserver/pkg/storage/testing/correctness` (`Model`, `Replay`, `WatchValidator`), used
the way `TestCorrectness` uses it (`test/integration/apiserver/storage/correctness_test.go`,
`testCorrectness`). Today the driver checks against its own Go copy of the Model (D30m). 7g builds
on 7f-6 E+F (branch `k8s-7f6`: `Check` over `lintest.RunLin2` with watchers, `kSpec`,
`watchOkL`, `KWatch`), which is landing now.

This Scope was a hard stop; **approved by the user on 2026-11-17, via etcd-grove-03** (§7). No Lean is edited and no translation regenerated. The Go experiment
(§8) runs in scratch (`/shared/tmp/k8s7g/`). Its driver diff and tests are committed as
`notes/k8s-7g-experiment.patch`, against `k8s-7f6`, with the D30g patch as `notes/k8s-7g-d30g.patch`.

**In one paragraph.** Upstream's checker is only defined on histories where no call failed:
`TestCorrectness` panics on any error that is not a `StorageError`. The Go runs confirm it. Every
partitioned run with a failed unary call is `Illegal` under the real Model, while the driver's model
accepts it (§8). So 7g **adds** the real checker after the driver's own check and does not replace
it (design A', Q1):

- `Check` runs `RunLin2` with the driver's model as now;
- if that run is `Ok` and no call failed, `Check` runs `TestCorrectness`'s pipeline with the real
  code on the same history: porcupine over `correctness.Model`, `NewReplay` along porcupine's
  linearization, `Replay.Validate` of every operation, `WatchValidator.ValidateWatch` of every
  watch;
- if the pipeline rejects, `Check` returns `Illegal` and `Main*` panics.

The conclusions do not change. They now also mean that the maintainers' checker accepts every
failure-free history. Four small driver changes make the real checker usable on the driver's
objects and seeded store (§1.4). Without them it rejects correct runs, as the experiment shows.

## 1. What gets translated, and how

### 1.1 The package (k8s.io/apiserver at the driver's pin `v0.0.0-20261021221356-9c4ec15b8038`)

| File | Lines | Translated | Notes |
| --- | --- | --- | --- |
| `types.go` | 201 | types; `Request.Describe` excluded | `Operation`, `Request`, `Response`, `Change`, `WatchRequest`/`WatchResponse`/`WatchOperation` |
| `model.go` | 567 (+ D30g patch) | with bodies, except `NewModelFromStorage`, `compact` (no compactions), `Describe` | 19 functions proved: `NewEmptyModel`, `Clone`, `Equal`, `Step`, `execute`, `validateGet`, `validateList`, `equalListResponse`, `validCacherContinue`, `listResponseRV`, `update`, `create`, `get`, `list`, `listItems`, `keyInScope`, `checkKey`, `initialEvents`, `delete` |
| `replay.go` | 200 | with bodies, except `Replay.Watch`, `ResourceVersion` (not on the validator's path) | `NewReplay`, `Validate`, `validateGet`, `validateList`, `InitialEvents`, `EventsForRVs` |
| `watch.go` | 419 | with bodies | 15 functions: `NewWatchValidator`, `ValidateWatch`, `checkWatch`, `validateInitialEvents`, `splitInitialEvents`, `validateMaybeLastEventError`, `validateReliable`, `compareEvents`, `validateBookmarks`, `toEventReference`, `Change.toWatchEvent`, `watchRevisionRange`, `eventResourceVersionRange`, `objectRV`, `filterOutBookmarksAndErrors` |
| `consistency.go` | 100 | with bodies | `GetReadConsistency`, `ListReadConsistency` |
| `storage.go` | 156 | excluded | `ModelStorage`, the Model as a `storage.Interface` (for upstream's scenario tests; not the checker) |
| `correctness.go` | 2839 | excluded | upstream's table of Model test steps (imports `testing` and testify) |

That is 42 functions with specs and proofs. `TestCorrectness`'s glue (`ToPorcupineModel`,
`toPorcupineOperations`, `orderByLinearization`, and the 30 lines of `testCorrectness` that run the
pipeline) lives in the Kubernetes test file, not in the package. The driver keeps a copy of it, as
statement-level text in the sense of D30m (§3).

**Where the patched source lives (Q2).** Go's `replace` works per module, and the store is
translated from the same module `k8s.io/apiserver`, so a fork of the module would also change the
store's provenance. Instead, the five files are copied into the driver module as
`examples/k8s/etcd3/correctness/` (package `correctness`), with the D30g patch applied. A new gate,
`etc/k8s-correctness-check.py` (in `etc/gates.sh` and CI, like `etc/prophcheck`), takes the five
files from the module cache at the pin in `examples/k8s/etcd3/go.mod`, applies
`etc/k8s-correctness/d30g.patch`, and requires the copy to be identical. So the copy is upstream
plus one named patch, mechanically. The goose project `k8s-apiserver` gains the package `./correctness`
(module `Code.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness`) with a
`correctness.toml` listing the exclusions above.

### 1.2 What Goose cannot take: the trust-boundary specs (each with its Go evidence)

| Callee | Where the checker calls it | Spec (stated at the driver's types only, as `reflect.DeepEqual.spec_pgidSet`) | Go evidence |
| --- | --- | --- | --- |
| `reflect.DeepEqual` | `Model.Equal` (`map[string]runtime.Object`); `Step` and `validateGet`/`validateList`, `equalListResponse` and `Replay.validateGet` (`Response`); the no-op check of `update` and `compareEvents` (`runtime.Object`); `ValidateWatch` (`error`, unreachable: `checkWatch` returns nil on the driver's requests) | one axiom over a deep-value view `deepRep v d` of the dynamic types the driver reaches. `*Obj`: its record. `*ObjList`: whether Items is nil, the items, RV, Continue, and whether RemainingItemCount is nil plus its pointee. `*storage.StorageError`: code, key, RV and the inner error. `*errors.errorString`: its text. A nil interface is its own view. `Response` is the pair of its fields' views, `map[string]runtime.Object` its key set with each value's view. **`DeepEqual(a, b)` is `da = db`**; values of different dynamic types are never equal | `reflect/deepequal.go`'s rules; `TestDeepEqualFacts` (22 cases, pass): objects by their fields, the annotation bit included; **a nil and an empty `Items` differ**; the remaining count by its pointee; two `NewInvalidObjError` with one message are equal; sentinels by identity or text; an empty and a nil map differ |
| `cmp.Diff` (go-cmp) | `compareEvents` on `[]eventReference`; its other calls are on error-message paths, which the proof shows unreachable | for two **non-nil** slices: returns `""` iff the slices are equal element by element (`==` on `Key`, `Type`, `ResourceVersion`). `toEventReference` always makes a non-nil slice (`make(…, 0, n)`) | `TestCmpDiffEventRefs` (11 cases, pass), in package `correctness`. **A nil and an empty slice differ under `cmp.Diff`**, so the spec takes non-nil |
| `maps.Keys`, `slices.Sorted` | `Model.list`, `Model.listItems`: `slices.Sorted(maps.Keys(s.Items))` | at `map[string]runtime.Object`: `Keys` returns an iterator yielding each key once; `Sorted` returns the keys in increasing order | Perennial translates no `maps`, and `slices.Sorted` is names-only. Both are generic standard-library functions, small and translatable. **Proposed to Perennial as an independent change** (translate `maps.Keys`/`Clone`/`Equal` and `slices.Sorted`/`Collect`/`AppendSeq`; `notes/perennial-changes.md`). Until it lands: local specs |
| `maps.Clone`, `maps.Equal` | the D30g patch (`Clone`, `Equal` of `NeedsRewrite`) | at `map[string]bool`: a fresh map with the same entries; true iff the same entries | as above. (The patch could use loops instead; it keeps upstream's idiom, Q3) |
| `meta.SetList` | `Model.list` | proved over the existing `reflect` axioms (7e's `MakeSlice`, `Value.Set`, …) if `meta`'s translation has its body; otherwise one spec at `*ObjList`: Items is set to the objects' records, non-nil | `TestDeepEqualFacts`' list cases and the runs (the Model's list `DeepEqual`s the store's) |
| `apierrors.SuggestsClientDelay` | `validateGet`, `validateList` | false on every error the driver sees except a too-large error, where it may be either | read from `k8s.io/apimachinery/pkg/api/errors` at the pin. A proof if the package's translation reaches it |
| `strconv.FormatUint`, `strconv.ParseUint` | the Model's `SetResourceVersion(strconv.FormatUint(rv, 10))`; the driver's `Obj.SetResourceVersion` (§1.4) | Perennial proves `ParseUint`. `Spec/strconv/FormatUint.lean` exists (raft's). Needed: `ParseUint(FormatUint(n,10),10,64) = n` | Perennial's `strconv` model |
| existing specs | `storage.PrepareKey`, `PrepareContinueToken`, `SelectionPredicate.Matches`/`Empty`, `Preconditions.Check`, `NewKeyNotFoundError`, `NewKeyExistsError`, `NewTooLargeResourceVersionError`, `IsTooLargeResourceVersion`, `IsNotFound`, `HasInitialEventsEndBookmarkAnnotation`, `apierrors.IsTooManyRequests`, `meta.Accessor`, `meta.ListAccessor` | already specified for 7b-7f (the storage package is translated with bodies) | -- |

Every `panic` in `Model.list` and `checkWatch` (nil selectors, limit/continue, limit with RV `0`,
selectors without `GetAttrs`, `RecordTimestamps`, legacy initial events, initial events without
bookmarks) is proved unreachable from the driver's request invariants (`kInOk`, `WatchInOk`). The
`fmt.Errorf`/`Sprintf` calls on the checker's failure paths need no spec: the proof shows those
paths unreachable.

### 1.3 D30g's fix, as a patch until upstream takes it (`notes/k8s-7g-d30g.patch`, 12 lines added or changed)

`Model` gains `NeedsRewrite map[string]bool`, the keys whose stored data the storage rewrites on
an update that leaves the object unchanged: data not in the codec's current encoding, or reported
stale by the transformer (`GuaranteedUpdate` writes it, #48394). The changes:

- `update` takes the no-op shortcut only when `!s.NeedsRewrite[key]`;
- `update`, `create` (unchanged: the key is absent) and `delete` clear the key's entry when they write;
- `Clone` copies the map and `Equal` compares it.

With an empty map it is upstream's Model, so for a canonical store it is the identity. The driver's
initial Model sets the entry for each seed written in the older encoding (`canon = false`). Upstream
form: a field (or a constructor option) like this; the upstream report is the
`k8s-correctness-model-noop-rewrite` nonissue's, through the `upstream-report` skill, later.

**Go test** (`TestD30gRealModel`, pass). A seeded non-canonical key gets a no-op update. The store
rewrites it at a new resource version, and the driver's model (the store's rule) says the same.
The unpatched real Model rejects that response (`Step` returns false). The patched one accepts it,
with a change.

### 1.4 The driver changes the real checker needs (each found by the experiment, §8)

1. **`Obj.SetResourceVersion` parses a decimal string** (`strconv.ParseUint`; `""` is 0). Today it
   does nothing. The Model sets an object's resource version through the accessor with
   `strconv.FormatUint(rv, 10)` (Kubernetes' `APIObjectVersioner` form), and with the current no-op
   every model object keeps RV 0: the real porcupine run is `Illegal` (§8). `GetResourceVersion`
   keeps the versioner's 8-byte form, which preconditions and `objectRV` read. The asymmetry is
   harmless and stated in the docstring (Q6: the alternative is a decimal versioner throughout).
2. **`ObjList` implements `metav1.ListInterface`**: `Get`/`SetResourceVersion` (versioner form),
   `Get`/`SetContinue`, `Get`/`SetRemainingItemCount`, and an empty self link. `meta.ListAccessor` is
   on the checker's list path (`listResponseRV`, `Replay.validateList`, `equalListResponse`).
3. **The drawn resource versions are raised to the seed revision** (departure D7g-1, Q4). The
   replay knows the states from the initial Model's revision on, and the driver's seeds put that
   revision at 3: two writes in the older encoding at revisions 2 and 3 of a fresh cluster. An Exact
   list at RV 1 or 2 is answered correctly by the store and accepted by the driver's model, which
   carries the history from revision 1. The real `Replay.validateList` rejects it with "resource
   version 1 not found in history" (18 and 21 such failures per run, §8). `TestCorrectness` runs on
   a fresh etcd, so its "RV 1" is its initial revision. The driver maps every drawn RV in `[1, st0.rv)`
   (Gets, lists and watches: "one", "past" clamped, and a cached object of revision 2) to `st0.rv`.
   With the floor, 0 failures (§8).
4. **The real checker's inputs** come from the recorded history:
   - each `Output` gains `Raw`: the store's actual `runtime.Object` and `error` (unary) or the
     received `[]watch.Event` (a watch);
   - the `correctness.Request` is built from the `Input` (the closures `tryUpdateFor(in)` and
     `validateFor(…)` are pure functions of it, so building them at check time is the same as at
     call time);
   - **a watch's events are cut after its first Error event** (departure D7g-2, Q5): upstream's
     harness reads nothing more and the validator requires the Error to be last;
   - **a watch-list whose events end before the initial-events-end bookmark is given to the real
     validator with no events** (departure D7g-3, Q5): the validator rejects such a watch ("missing
     initial events end bookmark") although the consumer's timer, or an Error, can cut it there.
     Upstream's harness has the same timer, so this is a latent flake upstream (new nonissue
     `k8s-correctness-watchvalidator-cut-before-bookmark`);
   - skipped watches are omitted.

   The driver's own check keeps seeing every event (the 7f departures stand).

The new `Check` (sketch):

```go
r, lops := lintest.RunLin2(Model(st0, h0), apply, gen, clock, clients, ops, watchers, wops, timeout)
if r != porcupine.Ok || !failureFree(lops) {
    return r                                   // the maintainers' checker is undefined here (§2.1)
}
if !realCheck(initialModel(st0), lops, timeout) {  // porcupine(Model) → NewReplay → Validate → ValidateWatch
    return porcupine.Illegal
}
return porcupine.Ok
```

`failureFree`: no unary output `EOther`, and no watch whose `Watch` call failed. `realCheck`
returns `Unknown` only when porcupine times out (`timeout > 0`; the theorems' `Main*` pass 0).

## 2. The real verdict and the existing pure model: what carries over, the bridge

### 2.1 Why the driver's own model stays (design A', Q1)

`correctness.Model.Step` answers `false` to any failed call. For writes, `DeepEqual(expected,
output)` fails on a client error, and `TooManyRequests` on a write panics. For a consistent read,
the expected response differs. `TestCorrectness` panics on such errors (`runTraffic`), so the
maintainers' checker is only defined on failure-free histories. The cluster and partition theorems
must hold in runs with failed writes: five of the six partitioned runs had 1-3 failed calls and
were `Illegal` under the real Model (§8). So the driver's model (`kSpec`: pending failed writes,
per-configuration histories) keeps deciding there. It also gives the linearization that the
bridge to the real checker starts from. Replacing it would need the failed-write trap of
`notes/k8s-7d-scope.md` §2 solved inside upstream's Replay. That is not 7g's.

### 2.2 What carries over unchanged

All of 7b-7f-6: the store's specs and their proofs, `kSpec`/`kstepL`, `KRelH`, `watchOkL` and the
bridge `streamOkL_of_kStreamOk`, `RunLin2`'s spec and linearization, and `Check`'s current proof up
to the `RunLin2` call. The real checker is an extra phase after it. Its proof needs only:

- the `Ok` post of `RunLin2.spec`: `IsLinearization (pM (kSpec h0) decOp) (histOf lops) (range n)`;
- `opsIoOk`;
- the new `Raw` facts in each output's `ioOk`.

### 2.3 The bridge theorem

**B (the bridge).** For the seeded store `st0` with history `h0`, and the history `lops` that
`RunLin2` returns linearized by `kSpec`, assume:

- `failureFree lops`, and every drawn RV is 0 or at least `st0.rv` (the floor);
- each output's `Raw` is the deep value its plain fields encode (from `call`'s and `runWatch`'s
  posts).

Then:

- (i) the unary history converted to `correctness.Operation`s is `Linearizable` for `realS`, the
  `ModelSpec` of `correctness.Model` (so the real porcupine run, with timeout 0, answers `Ok`);
- (ii) for **every** linearization `lin2` of it for `realS`, `NewReplay(init, lin2)` succeeds,
  `Replay.Validate` accepts every operation, and `WatchValidator.ValidateWatch` accepts every
  converted watch.

Statement (ii) has to hold for any `lin2` because porcupine's second run may pick a different
linearization than the driver's.

**Its pieces (pure Lean, `Proof/.../k8s/etcd3/Real*.lean`):**

- **B1, one step.** The real model's `execute` on `absR st` equals `mstepL in st` under
  `absR : mstore → RM` (key ↦ `storeKey key`, item ↦ its `Obj`, `canon` ↦ not in `NeedsRewrite`)
  and `respOf : Output → RespD`. So does its list, as `mlistL` on the current store: the sorted keys
  of `maps.Keys` are `mstore`'s key order. And `validateGet`/`validateList` accept what `kstepL`
  accepts: for stale reads they check only the RV, which `mgetL`/`mlistL` satisfy.
- **B2, linearizability transfer.** With no failed call, `pM (kSpec h0)` keeps one configuration
  with no pending write. Watch steps do not change the state, and failed reads do not occur. So the
  unary projection of `kSpec`'s linearization is a linearization for `realS` (by B1).
- **B3, the states are determined by the responses.** In a failure-free history, every write that
  bumps the RV answers with its object at the new RV (create, a writing update, delete). The
  writes that do not bump it (no-op updates, failed preconditions, rejected callbacks) leave the
  state unchanged. So in **any** linearization for `realS`, the writes that bump the RV appear in
  the order of their response RVs. The state at each RV `r` (and the change at `r`) is the same
  function of the history, and equals the driver's `histAt r` for `r ≥ st0.rv`.
- **B4, the replay checks.** Along any `lin2`:
  - `NewReplay` succeeds, because each step is allowed (`IsLinearization`).
  - A stale Get matched the current state at its `kSpec` point. By B3 that state is
    `states[rv]` for some `rv ≥ reqRV`, so `Replay.validateGet` finds it.
  - An Exact list read `histAt req` with `req ≥ st0.rv` (the floor). A NotOlderThan list read the
    current state. By B3 either one is `states[respRV]`, and B1-list gives `equalListResponse`.
- **B5, watches: `watchOkL` ⇒ `ValidateWatch`** (on the converted events, D7g-2/3). The 7f Scope
  §9 predicted that upstream's validator refines ours except at departures 1-2: D7g-2/3 handle
  exactly those. Checked piece by piece:
  - `validateMaybeLastEventError`: after the cut, an Error is last, and its status is `Failure`
    (otherwise `toWEvent` made it `WBad`, which `watchOkL` rejects).
  - `validateBookmarks` ↔ `bookmarksOk`.
  - `splitInitialEvents`/`validateInitialEvents` ↔ `watchListOk`. This needs the bookmark's RV
    `≥ st0.rv` so that `states[bookmarkRV]` exists. That is a fact of the store's watch (a
    bookmark at or after the store's revision at the call, which is after the seeds). It is to be
    read off `kStreamOk`'s `kStartOk`: R3.
  - `validateReliable`'s `EventsForRVs` over the replay's changes ↔ `reliableOk` over the
    configuration's history: same changes by B3, and the events' and bookmarks' RVs are at most the
    configuration's revision (departure 4's bound).
  - `compareEvents` (`cmp.Diff` of references, then `DeepEqual` of objects) ↔ `eventsEqual`.
  - `checkWatch` returns nil (`WatchInOk`).

**The Go side.** One spec per correctness function over `RM` (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/correctness/*.lean`,
as the driver's model functions are specified over `mstore`): each equals a pure Lean function
(`rstepL`, `rlistL`, `rvalidateGetL`, `replayL`, `validateWatchL`, …). The Model's
representation is persistent: `Step` never mutates the receiver, since `execute` clones and the
clone is frozen (`↦□`) when `Step` returns. This is what porcupine's `stepSpec`/`equalSpec`
need. `Equal` true implies equal `RM` (by the `DeepEqual` axiom and `maps.Equal`).

## 3. The closed statements, old → new

| Theorem | Change |
| --- | --- |
| `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe` and their `_adequate` | **text unchanged**: same binders, premises and conclusion (returns `Ok` or `Unknown`, not stuck, no panic). The programs `k8setcd3Program`/`CProgram`/`PProgram` are the same Go entry points, whose `Check` now runs the real checker too. Docstrings and "In plain English" gain: "and when no call failed, Kubernetes' own checker (`correctness.Model` through porcupine, `Replay.Validate` along its linearization, `WatchValidator`, with D30g's patch) accepts the history" |
| `k8setcd3_Main`, `_MainCluster`, `_MainPartition` (`Main*.spec`) | unchanged text |
| `Check.spec` (internal, not exported) | unchanged post (`r ≠ Illegal`, `Ok` with timeout 0) |

**New premise: none expected.** Two things to watch:

- The second porcupine run spawns goroutines (`checkParallel`). `CheckOperationsVerbose.spec`
  takes no thread token, and `RunLin2` already calls it once, so the thread bound is not expected
  to move (R5).
- The `Raw` objects need persistent ownership in the history (`↦□` of the store's `out` objects
  and of the watch events' objects). The store's specs already give the objects. Its errors need
  R1.

**What a reader must now trust as statement-level text (D30m).** Before: the driver's own Model,
watch check and traffic. After: the same, plus:

- the copied `correctness` package (upstream plus `d30g.patch`, enforced by the new gate);
- the driver's glue: `toPorcupineModel`, `failureFree`, the conversions and their cuts D7g-2/3,
  and the seed floor D7g-1.

The driver's model stays (it decides the runs with failures), so no text is removed.

## 4. The trust base, delta

| | Axioms | Notes |
| --- | --- | --- |
| added | `reflect.DeepEqual.wp_proof_k8sDeep` (one, over `deepRep`) | the driver's dynamic types only |
| added | `cmp.Diff.wp_proof_eventRefs` | non-nil `[]eventReference` |
| added, until Perennial translates them | `maps.Keys`, `slices.Sorted`, `maps.Clone`, `maps.Equal` (4) | at `map[string]runtime.Object` / `map[string]bool` |
| maybe added | `meta.SetList` (if not provable over the existing `reflect` axioms), `apierrors.SuggestsClientDelay` (if not translated) | 0-2 |
| added | `correctness`'s package-init axioms from `etc/gen-init.py` (`opaqueInitsOk` if the package has untranslated initializers; it has no package variables) | 0-1 |
| removed | none | |
| `sorry` | none added | |

Expected `etc/tcb-report.py --check` diff: +6 to +10 axioms, 0 `sorry`. The k8s collection gains
the same.

## 5. Steps, with Lean-line estimates and checkpoints

Starts after 7f-6 E+F has landed. Each step lands on its own when the coordinator says go. Steps
1-2 are hard stops, because they change trusted text and the trust base.

| Step | Contents | Lean lines | Checkpoint |
| --- | --- | --- | --- |
| **0. Go** | the copy, the patch and the gate; the driver changes of §1.4 (`Obj.SetResourceVersion`, `ObjList`'s accessors, the floor in `minRV`/`genWatchFrom`, `Output.Raw`, `failureFree`, the conversions, `toPorcupineModel`, `realCheck` in `Check`); the tests of §8 kept in the package; the translation (`correctness.toml`, the project's packages) | 0 | Go tests and repeated runs (§8's) green; `etc/goose.py --check`; the translation elaborates. **Report** |
| **1. Trust specs** | §1.2's specs with their Go evidence in the docstrings; an `axiom`-skill review of the `DeepEqual` view and the `cmp.Diff` spec | 400-700 | **hard stop** (trust base) |
| **2. The real model, pure** | `RM`, `rstepL` (create/update/delete/get/list/validate*), `replayL`, `validateWatchL` (`toWatchEvent`, the range, initial events) | 800-1300 | -- |
| **3. Go proofs of `correctness`** | the 42 functions, over §1.2 and the pure functions | 3000-5000 | per file (model, replay, watch, consistency); report at each |
| **4. Bridges** | B1 500-900, B2 400-700, B3 500-900, B4 300-600, B5 800-1500 | 2500-4600 | B3 and B5's statements first (**report**) |
| **5. The driver** | re-proofs: `minRV`, `genList`, `genWatchFrom` (the floor: `kInOk`/`WatchInOk` kept), `call`/`Apply`/`runWatch` (`Raw` and its `ioOk`), `ObjSpec` (`SetResourceVersion`), the new `ObjList` methods, `initialModel`, `failureFree`, the conversions, `realCheck`, `Check` | 1200-2000 | -- |
| **6. Link and close** | link lists, `Link`/`MainLinked`, the three theorems re-checked (text unchanged), `Results` docstrings and `#print axioms`, interfaces, the tcb collection, STATUS | 200-400 | **Freeze package** (hard stop) |
| total | | **8100-14000** | |

For scale: the driver's own model plus its watch check is about 9k lines of specs and proofs on
`k8s-7f6`. The real checker is more general (runtime objects, maps, errors), and the bridges are
new.

## 6. Risks

- **R1. The store's invalid-object error must be exact.** The real Model `DeepEqual`s a failed
  precondition's whole error. That includes the inner `errors.New(fmt.Sprintf("Precondition failed:
  UID in precondition: %v, UID in object meta: %v", …))`. Today `storage.invalidErrIs err key`
  leaves the inner error `∃ e`. It must become `invalidErrIs err key msg`, with `msg` the message
  of `Preconditions.Check` on the object the model sees. That is a ledger entry and a change to
  `GuaranteedUpdate`/`Delete`'s posts. The store checks the cached object first, but re-reads before
  failing (`!origStateIsCurrent`), so the final message is the current object's. The runs agree
  (`Step` accepted every failed-precondition response). It also needs Perennial's `Sprintf` model to
  be deterministic for `%v` of strings. It is meant to be, but must be checked (`SprintfOut`).
- **R2. Empty lists' `Items`.** `DeepEqual` tells nil from empty. The Model's `SetList` makes a
  non-nil empty slice, and the runs show the store's matches. The 7e `GetList` post must say so
  (a strengthening if it does not).
- **R3. The bookmark at or above the seed revision** (B5): it must be read off the store's watch
  spec. If `kStreamOk` does not give it, it is a store-spec strengthening (or the floor makes it
  moot for pinned watch-lists, but not for unpinned ones).
- **R4. Bridge B5's size.** `watchOkL` was written as the validator with departures, but its
  history is a configuration's (a prefix), while the replay is the whole linearization. B3 and the
  RV bounds connect them. If a gap appears, it is a strengthening of `watchOk`, which would be a
  change to checker text (a stop).
- **R5. The second porcupine run** costs time (not in the theorem) and goroutines (R5 of §3).
- **R6. Translation.** Generic calls (`maps.Keys`, `slices.Sorted`, builtin `min`/`max`, which goose
  supports), range over a map (`Clone`, `Replay.validateGet`'s existential loop: the proof must not
  depend on the order), and `cmp`/`testify` imports: `correctness.go` is excluded, `cmp` is
  names-only. The prototype was run in Go only; the goose dry run is step 0.
- **R7. Coordination**: 7f-6 must land first. Upstream may change the package. The pin is fixed
  by the driver's `go.mod`, and the gate catches drift.

## 7. Open questions, each with a recommendation

**Decided (2026-11-17): approved by the user, via etcd-grove-03.** Design A' (Q1) and the
recommendations on Q2-Q8, as written below. Step 0 starts after 7f-6 E+F lands. Step 1's
trust-spec texts and step 6's Freeze stay hard stops.

- **Q1. Design.** Should the real checker be added after the driver's check (A': run only on
  failure-free histories, conclusions also mean "the maintainers' checker accepts"), or should it
  replace the driver's model (B: the theorems say nothing about runs with failed writes, or need a
  failed-write lift of upstream's Model and Replay)? **Recommended: A'.** It is the maintainers'
  checker exactly where it is defined (`TestCorrectness` panics otherwise). It keeps every existing
  proof. It weakens nothing.
- **Q2. Where the patched package lives.** **Recommended:** a copy in
  `examples/k8s/etcd3/correctness/` with the gate `etc/k8s-correctness-check.py` (upstream at the pin
  plus `d30g.patch`, byte for byte). The alternative, a fork of `k8s.io/apiserver`, would move the
  store's source too.
- **Q3. The D30g patch's form.** **Recommended:** the field `NeedsRewrite map[string]bool` as in
  `notes/k8s-7g-d30g.patch`, upstream's idiom (`maps.Clone`/`Equal`). Report it upstream through
  the `upstream-report` skill when the user wants it public. The patch stays until then.
- **Q4. Departure D7g-1, the seed floor.** **Recommended: accept.** It is the faithful reading of
  `TestCorrectness`'s "RV 1" (its fresh etcd's initial revision). The cost is that the driver no
  longer reads below revision 3, which only the seeds' own states had. The alternative is to drop
  the non-canonical seeds (D30g's coverage, the user's decision of 2026-10-22), or a second patch
  to upstream's Replay.
- **Q5. Departures D7g-2 (events cut after the first Error) and D7g-3 (a watch-list cut before its
  bookmark shown as empty).** **Recommended: accept both.** The driver's own check still sees every
  event. D7g-2 is what upstream's harness reads. D7g-3 avoids a rejection that upstream's own
  harness can hit; a new nonissue says so.
- **Q6. The resource-version string form.** **Recommended:** keep the driver's 8-byte versioner and
  make `Obj.SetResourceVersion` parse decimal (one method, one proof). The alternative is to make
  the driver's versioner decimal throughout, as `APIObjectVersioner` is: cleaner, but it touches
  `parseRV`/`rvString`/`rvBytes` and every proof over the inputs' RV strings, an estimated
  +1000-2000 lines.
- **Q7. `Output.Raw` (the store's actual objects and errors) or a reconstruction from the plain
  fields.** **Recommended: Raw.** The real checker must judge what the store returned. A
  reconstruction would have the driver compute the precondition messages it is meant to compare. It
  costs R1.
- **Q8. `maps`/`slices.Sorted`.** **Recommended:** local specs now, and a general Perennial change
  proposed on its own (translation only, no new assumption). The four local axioms go when the pin
  moves to it.

## 8. The Go experiment (scratch `/shared/tmp/k8s7g/`; `GOWORK=off`, go1.27.3, `MemoryMax=32G`)

The k8s-7f6 driver, with the copy of `correctness` (patched or not) and the changes of §1.4 behind
switches. `realcheck_test.go` records the store's raw requests and responses beside the driver's
check (`RunLin2` with `Model`). It then runs `TestCorrectness`'s pipeline on the same history, with
the driver's linearization giving each operation its call and return times.

| Test | Result |
| --- | --- |
| `TestD30gRealModel` | unpatched Model rejects the store's rewrite of a non-canonical seed; patched accepts (pass) |
| `TestDeepEqualFacts` (22 cases), `TestCmpDiffEventRefs` (11 cases) | pass; found: nil and empty `Items` differ under `DeepEqual`, and nil and empty slices differ under `cmp.Diff` |
| `TestValidatorDepartures` | upstream's validator rejects an Error that is not last and a watch-list cut before its bookmark; accepts both after D7g-2/3; an Exact list below the initial RV is "not found in history" (pass) |
| `TestRealChecker` (one member, 8 × 300 unary, 16 × 8 watches), **no floor** | driver's check `Ok`; real porcupine `Ok`, `NewReplay` ok, **18 and 21 `Validate` failures, all "resource version 1 not found in history"** (two runs, patched and unpatched); every watch accepted |
| same, **`SetResourceVersion` a no-op** (today's driver) | **real porcupine `Illegal`** |
| same, **with the floor**, patched, decimal `SetResourceVersion` | **5 of 5 runs: the real checker `Ok`** (2400 unary, 36-75 watches each, every one validated) |
| `TestRealCheckerPartition` k = 3, with the floor: `election` ×2, `isolate`, `mixed`, `drop`, `blackhole` | driver's check `Ok` in all six; **real porcupine `Illegal` in the five runs with 1-3 failed unary calls**; `Ok` in the one failure-free run (`blackhole`, 75 watches validated). (An earlier batch, k ∈ {1, 3} × six schedules, ran without its schedules by a test bug, so it shows only failure-free cluster runs: 12 of 12 `Ok`) |

Commands, in the handoff. The unpatched Model never met a no-op update of a not-yet-rewritten seed
in the full runs. That case is rare in the traffic, and `TestD30gRealModel` shows it directly.
