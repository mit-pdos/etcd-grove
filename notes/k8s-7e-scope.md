# k8s etcd3 stage 7e, lists: Scope, revision 2 (2026-11-08, branch `k8s-7e`; approved by etcd-grove-81 2026-11-08 after an independent recheck, with the additions in §4.1 and §7)

**Changes from revision 1.** These answer the independent review (`/shared/tmp/k8s-7e-scope-review.md`,
wf_581c2266-9a1). It confirmed design (b) is sound. The changes carry 81's decisions of 2026-11-08,
Q7e-5 being the user's:
- **Q7e-5, streaming.** The driver turns `EtcdRangeStream` off, and featureInit becomes a
  gate-state fact (§4.1). Streaming is its own stage right after 7e. The coverage is stated as the
  paginated path, which about 45% of the test's lists take (§1).
- **Q7e-1.** The continue token is compared by its bytes, through one opaque `encL`.
- **Q7e-2.** The driver supplies its own selectors and covers all of the test's.
- **Q7e-3.** The four two-level keys, with the namespace/name split and the seeds' revisions
  checked. `hist[1]` is empty.
- **Q7e-4.** The order and the extra Go tests (§9).
- **ETooLarge.** A new output, compared.
- **7c-3.** Stays its own landing. §7 lists the re-proved results and the interface files.
- **`mlist` and `hist`.** `mlist` follows upstream's loop for has-more and the remaining count.
  `hist` grows only with the revision.
- The Go pitfalls fixed, §2 and §4 corrected, the estimate redone per stage.

No Lean until 81 approves. Stage 7e-0 (Go only) may start once this revision is in. The pins are
7d's: `k8s.io/kubernetes` `878cfa6c4cc7`, `k8s.io/apiserver` `9c4ec15b8038`, etcd fork `673da07c8f`.

## 1. The traffic the test sends, and what 7e covers

`correctness_test.go:84-125` and `traffic.go:376-418`, confirmed by the review. Lists are 25% of
the unary operations. Each list draws:
- **a scope**: cluster `/pods/` (50%), namespace `/pods/<ns>` (25%), object `/pods/<ns>/<name>`
  (25%). Then **`Recursive` is drawn again** (true 70%, false 30%) and overrides the scope's own;
- **a field selector**: everything 25, by name 15, by namespace 15, by node 20, by empty node 15,
  combined 10. **A label selector**: everything 60, by app 40 (`pickPredicate`, `traffic.go:629-678`);
- **a resource version** as for Gets. With a non-empty RV, **a match**: `""` 50, `NotOlderThan` 25,
  `Exact` 25. `Exact` with RV `"0"` is dropped;
- **a limit**, only when RV ≠ `"0"`: 0 70, 1 15, 2 15. `Predicate.Continue` is never set.

The test's four objects test prefix boundaries: `ns-1/pod-1`, `ns-1/pod-11`, `ns-2/pod-2`,
`ns-11/pod-1`.

**The driver follows all of this** (Q7e-2, Q7e-3), with three deviations. Each is stated in its
docstring:
- the resource prefix is `/objs`, and two of the four keys are seeded before the traffic (D30g);
- **the RV modes are relative to the client's cached object** (`minRV`), not to
  `GetCurrentResourceVersion` as in the test. The test's "future" is always too-large; the
  driver's is often a valid past revision. §8's counts confirm that the too-large list path is
  still reached. Moving to GetCurrentResourceVersion-relative RVs (its spec exists:
  `store__GetCurrentResourceVersion.lean`) is a possible follow-up;
- the test's literal `"0"` checks map to the driver's `rvBytes(0)` (an 8-byte string, empty RV
  `""`): the driver drops `Exact`, and drops the limit, whenever the RV parses to 0 and is
  non-empty.

**Coverage (Q7e-5).** With `EtcdRangeStream` on, its default at the pins, `shouldStream`
(`store.go:748-760`) sends every recursive list through `streamChunks`/`KV.GetStream`, except
those with `Limit > 0` and a non-empty predicate. The review's weighting: about 55% of the
test's etcd3 lists stream, and about 45% take `pagedChunks`.
- 7e turns the gate off, so all of the driver's lists take the paginated path. 7e therefore
  verifies **the paginated path, which about 45% of the test's lists take**, not the test's list
  path as a whole.
- The streaming path is the next stage (§9, 7s), reusing the server's RangeStream proofs
  (`v3rpc/checkRangeStreamRequest`, `headerFillingRangeStream__Send`).
- Scope, recursion, RV, match, limit and both selector families are covered 100% within the
  paginated path.

## 2. Which lists are stale in the etcd3 store

`storage.ValidateListOptions` (`interfaces.go:372-410`) and `GetList`/`pagedChunks`:
- **at the latest revision** (`withRev = 0`, then fixed to the first page's revision for later
  pages): no RV, RV `"0"`, `NotOlderThan` (then `validateMinimumResourceVersion` against the read
  revision: too-large if above), and **legacy `""` unless `Recursive`, `Limit > 0` and `RV > 0`**.
  These answers are linearizable, and the model checks them exactly, as it checks Gets
  (upstream checks only `NotOlderThan`'s resource version);
- **at a past revision** (`withRev = RV`): `Exact`, and legacy `""` with `Recursive`, `Limit > 0`,
  `RV > 0`. These are the stale reads, about 20% of the test's lists (the review's count).
  - Above the current revision: `ErrFutureRev`, which `listReadError` maps to
    `TooLargeResourceVersion`, after `GetCurrentResourceVersion`.
  - Below the compaction revision: `ErrCompacted` → 410. **No compaction happens** (no
    compactor, etcdstart's auto-compaction off, no `Compact` RPC from the driver). So 410 is
    unreachable, by the client spec's `ErrCompacted` soundness (7c) plus the server's compaction
    revision staying at its initial value. That fact is taken from the hub's state at 7e-1 (the
    review's dropped minor, folded there).

## 3. The design: the history in the model (7d Scope §2 (b))

**Configurations.** `mcfg` gains `hist []mstore`, indexed by revision: `hist[R]` is the store at
revision `R`, for `1 ≤ R ≤ st.rv`.
- **Only writes that bump the revision append.** The no-op update of a canonical item, and the
  rejected, invalid and not-found outcomes, keep `st` and `hist`.
- `len(hist) = st.rv` is an invariant, asserted in Go tests.
- A pending failed write appends when it takes effect, in the configurations where it does.
- Each configuration keeps its own history. `closure` applies pending writes in every order, so
  the configuration matching etcd survives. **No replay is needed for soundness**: porcupine is
  complete, and the real linearization keeps the real history (confirmed by the review).

**The initial history (Q7e-3).** `seed` observes the seeds' revisions from the `Put` headers.
`Main`, `MainCluster` and `MainPartition` return `Unknown` unless they are 2 and 3.
- `hist = [⊥, {}, {a}, {a, b}]`: index 1 is the empty store of a fresh server, revisions 2 and 3
  the seeds.
- The Lean obligation: the server's `stateAt 1` is empty (a fresh start's read log).
- The invariant covers every `R ≥ 1`.

**`mlist(in, c)`** is upstream's `Model.list` loop (`model.go:394-460`) on a store `s`:
- `s` is `c.st` for a latest-revision mode, and `c.hist[RV]` for a past-revision mode;
- too-large if the RV is above `c.st.rv`;
- iterate the keys in scope in sorted order. Scope uses `keyInScope`: exact key if not
  recursive, else prefix with the `/` boundary;
- `totalCount` counts the keys in scope;
- **`hasMore` is true iff some key in scope (matching or not) follows the limit-th match**
  (upstream's `limit > 0 && len(items) >= limit` at a later key; etcd3's `limitReached` at the
  next kv);
- the items are the first `limit` matching ones;
- the continue token is `encL(lastKey + "\x00", prefix, listRV)` when `hasMore`;
- **`remainingItemCount = totalCount - Limit` iff `hasMore` and `Predicate.Empty()`**, else none
  (`PrepareContinueToken`, `continue.go:100-122`);
- the list RV is the requested RV for a past read, `s.rv` for a latest read.

**The step for a list compares the whole answer**: items, list RV, token bytes, remaining count,
and the too-large outcome.

**Outputs.** `Output` gains:
- the list's items (namespace, name, UID, value, node, RV), the list RV, the continue token
  (bytes) and the remaining count (with a has-it flag);
- **`ETooLarge`**: an error that `storage.IsTooLargeResourceVersion` recognizes, on an error known
  not to be the client's (7c's T2(c) exclusion: the client's errors are not `*StatusError`s).
  - The model answers `ETooLarge` for a list RV above the store's. For a Get it answers it for a
    minimum above, if cheap: `mget`'s `EOther` for that case becomes `ETooLarge`.
  - `errOut` gains the case.
  - Upstream's `validateList` also requires a model too-large: `NewTooLargeResourceVersionError`
    has `RetryAfterSeconds` 0, so `SuggestsClientDelay` is false.

**The continue token (Q7e-1).**
- The Go model calls the same `storage.EncodeContinue` the store calls, through
  `PrepareContinueToken`.
- In Lean, both sides go through one opaque deterministic `encL(key, prefix, rv) : GoString`. The
  trust-boundary spec: `EncodeContinue` returns `encL(args)` and no error for these inputs.
- **No injectivity claim**: JSON maps invalid UTF-8 to U+FFFD.
- The byte comparison checks the token's start key and RV, the only observable trace of
  pagination (the #94002 class).

**Selectors (Q7e-2).** The driver defines its own `labels.Selector` and `fields.Selector`
implementations, as verified driver code. The etcd3 path reaches only their `Empty` and
`Matches`, through `SelectionPredicate.Matches`/`Empty`; `ShardingEnabled` is false with a nil
`ShardSelector`. The selectors cover all six field and both label selectors of `pickPredicate`:
- fields everything, `metadata.name=`, `metadata.namespace=`, `spec.nodeName=`, `spec.nodeName=""`,
  and the combined one;
- labels everything and `app=`.

`GetAttrs` is total, since a `Matches` error silently drops the item (`store.go:1047-1049`):
- the namespace and name come from the object's fields;
- the node comes from a new field;
- the labels come from a new field (`app`), drawn as the test draws them.

**`Obj` (Q7e-3, costed separately in §9).** `Obj` gains `Namespace`, `Node` and `App`, with
`Name` the key's last component. Today `Name` is the whole key and `GetNamespace` returns `""`.
This touches:
- `encodeObj`/`decodeObj`/`encodeV0`;
- `sameObj`;
- the canonical bit (D30g);
- `contractOk` (7b);
- the metav1 accessors;
- `Gen`, `updated` and `validateFor` (which reject on a node, as the test's do).

## 4. The store side

### 4.1 The feature gate (Q7e-5)

- `Main`, `MainCluster` and `MainPartition` call
  `utilfeature.DefaultMutableFeatureGate.Set("EtcdRangeStream=false")` (or `SetFromMap`) before
  `etcd3.New`. A Go change.
- **`featureInit` (`Base.lean:58-64`, today "`Enabled` answers any bool") becomes a gate-state
  fact.** The gate holds a map of feature values; `Set` updates it; `Enabled(f)` returns the
  value set (or the default).
- It is written **by sweep repairs 1 (its B5, the k8s feature initializers), to serve both B5 and
  this stage** (81, 2026-11-08): one restatement, not two. 7e does not write its own; 7e-2's Draft
  uses exactly that interface (`/shared/tmp/sweep-repairs-1/b5-r1.md`, approved):
  `featureGateOk g` (persistent); `Set (s ++ "=false")` returns `nil` with a persistent
  `featureOff g s`, or an error; `Enabled s` returns `false` given `featureOff g s`;
  `features.EtcdRangeStream` translated to its string literal (a k8s-apiserver re-translation).
  The driver's `noStreaming` already calls `Set("EtcdRangeStream=false")` and returns `Unknown` on
  an error. It is new trusted text, attacked with the
  `axiom` skill before it is used.
- With the gate off, `shouldStream` is false and `streamChunks` is unreachable. The support
  checker's `Supports` is not called (`shouldStream` tests the gate first).

**Additions from 81's approval (2026-11-08)**, carried into 7e-2's Draft and the joint
restatement:
1. `features.EtcdRangeStream` is an opaque axiom constant in Lean (`features.toml` translates only
   `ListFromCacheSnapshot`). Translate it, or otherwise tie `Set`'s string
   (`"EtcdRangeStream=false"`) to `Enabled`'s key.
2. `DefaultMutableFeatureGate`'s initializer and `DefaultFeatureGate` are unlinked today
   (`opaqueInitsOk`, post `True`). The restated fact must say both hold the same
   `*featureGate`, and that registration happens in `features`' init (`initFuncsOk`).
3. The shape: monotone and persistent. `Set` is specified only for `false`, returning a
   persistent "off" witness that `Enabled` reads; no "or the default". `Set` can fail, so the
   driver returns `Unknown` on an error (as built in 7e-0: `noStreaming`).

### 4.2 The path

The path, with what each piece needs (the review's completions included):
- `GetList` (`store.go:763-860`), translated in 7a:
  - `prepareKey` is proved;
  - `meta.GetItemsPtr`, `conversion.EnforcePtr`, `getNewItemFunc` (`reflect.New(elem)`) and
    `growSlice` (`MakeSlice`/`Cap`/`Copy`) need local `reflect` trust-boundary specs. They are
    **stated for the driver's list type only (elem `Obj`), with `Append` consuming the old
    slice's ownership** (as Perennial's `slice.append`), and each attacked by the `axiom` skill;
  - the deferred metrics closure reads `v.Len()`: the same specs;
  - `listErrAggrFactory`/`Aggregate`: the store's existing no-op aggregator specs.
- `shouldStream`: §4.1.
- `storage.ValidateListOptions`: `DecodeContinue` is unreachable (no token sent);
  `ParseResourceVersion` is the driver's versioner (proved).
- `pagedChunks` (`iter.Seq2` with `yield`, G2) → `getList` (`store.go:1081-1100`):
  - **recursive**: `kubernetes.Client.List` (§5);
  - **non-recursive** (30% of lists): **`Client.Get` at a revision, 7c-3**, with `Count ≤ 1` and
    never has-more;
  - page doubling up to `maxLimit`.
- `appendChunk`/`processListItem`:
  - `decoder.DecodeListItem`: **new driver code** (today a stub returning `errNoList`). It calls
    `newItemFunc` and fills the object at the kv's `ModRevision`;
  - `SelectionPredicate.Matches` with the driver's selectors (§3);
  - `reflect.Append`/`Value.Set`/`Len`.
- `storage.PrepareContinueToken`: `EncodeContinue`'s spec through `encL` (§3), reached only when
  has-more.
- `finalizeList`:
  - `versioner.UpdateList` is **new driver code** (today a stub) and gives the contract a list
    half;
  - `SetShardInfoOnList`: a no-op with no shard selector (a spec or its translation);
  - `aggregator.Err()`.
- `listReadError`: `errors.Is(err, ErrFutureRev)` is 7c's identity. Then
  `GetCurrentResourceVersion` (**specified and proved already**,
  `store__GetCurrentResourceVersion.lean`) and `NewTooLargeResourceVersionError`.
  `interpretListError`'s 410 branch is unreachable (§2).

`GetList.spec` is logically atomic against the store's `KSt` plus its history: the answer is
`mlist` at one linearization point, the first page's read. Later pages read at the same
revision.

## 5. The client

- **7c-3 stays its own 7c landing with its own Freeze** (as approved in 7c's Scope).
  - `Client.Get` at any revision, through linkvtxn's `client_*` chain.
  - Its prophecy patch for the response's revision.
  - Its callers' glue (§7).
- **7e-1 is `kubernetes.Client.List` on top of it** (Q7e (a), approved in 7c's Scope):
  - a read update with a prophecy of the response's revision;
  - the answer at the state read is the keys of `[start, prefixEnd)` at the revision, sorted, the
    first `limit`;
  - `Count` is the keys in the range;
  - `Revision` is the header's (current) revision;
  - errors as `Get`'s.
- **Requirements found by 7e-2's Draft** (`notes/k8s-7e-2-draft.md` §4.5, §7; passed on by
  etcd-grove-81, 2026-11-08):
  - **7c-3:** the `*StatusError` exclusion (7b's T2 (c)) must state that a client error's dynamic
    type is outside `apierrors.APIStatus`'s type set (`typeSetContains t APIStatus.ty = false`) and
    is a leaf (no `Unwrap`/`As`), i.e. the Draft's `apiErrAt err .plain`, not only `t ≠
    *StatusError`: `IsTooLargeResourceVersion` tests with `errors.As` to the interface
    (`apimachinery/pkg/api/errors/errors.go:817-822`).
  - **7e-1:** `Client.List`'s post gives the response's `Kvs` slice owned (`↦*`, not `↦*□`):
    the store's `appendChunk` writes `kvs[i] = nil` (`store.go:1074`). Its errors meet the same
    leaf, non-`APIStatus` condition, and carry the future-revision soundness at the call's revision.

## 6. The model in Lean and the invariant

- **`KModel.lean`/`KSteps.lean`**:
  - `mcfg`'s Lean record gains `hist`;
  - `mlistL`, the pure loop of §3 (sort, scope with the boundary, predicate through the driver's
    selector semantics, limit, `hasMore`, remaining count, `encL` token);
  - `stepL` compares lists and `ETooLarge`;
  - `PendSpec`'s pending writes append to `hist` exactly when they bump the revision.
- **`Refine.lean`**:
  - `KRel` relates the store's `KSt` plus history to `st` plus `hist`;
  - `refine_list` relates `GetList.spec`'s answer to `mlistL`. It comes after 7e-2's Draft
    statements.
- **`Inv.lean` (`kInv`)**:
  - for the configuration matching etcd, `hist[R] = absK (stateAt R)` for every `1 ≤ R ≤` the
    current revision, from M2's read log;
  - the commits in `InvSteps.lean` extend it at each write that bumps the revision;
  - the seeding's invariant gives revisions 1-3.
- **`encIn`** (the inputs' countable encoding, `Inv.lean:58-69`) encodes the new input fields.

## 7. Premises, trust base, re-proved results, interface files

**New trust-boundary specs** (estimate 10-14, each through the `axiom` skill):
- `reflect`'s `New`/`MakeSlice`/`Append`/`Set`/`Len`/`Cap`/`Copy` for the driver's list type;
- `meta.GetItemsPtr`/`SetList`;
- `EncodeContinue` → `encL`;
- `SetShardInfoOnList` if not translated;
- `storage.IsTooLargeResourceVersion` (or its translation; `storage` is translated, so likely
  proved).

Not needed:
- selector axioms (driver code);
- a new `GetCurrentResourceVersion` spec (it exists).

`featureInit` is restated, not added (§4.1).

**`Assumptions` classes**: none added, provided every new spec is a local trust-boundary axiom and
no apimachinery package is newly translated. The `_safe` theorems then keep their per-package
binders.

**Re-proved results.** Statements are unchanged unless noted.
- **7c-3 (its own landing):**
  - every caller of `Client.Get.spec`: the store's `store__Get`, `store__getCurrentState`,
    `FirstRead`, `State`, `store__GetCurrentResourceVersion`;
  - the daemonset `apimodel` clients (`pod`/`node`/`daemonSet`/`revisionClient__Get`, linked results
    with no closed theorem);
  - every caller of the `client_*` chain (`client_Get_kv`, `client_range_any`, `kv.wp_Get`):
    `examples/etcd/txnlin`, `examples/etcd/compactwatch`, `examples/goose/prophkv`, the k8s
    compactor.
  - Closed theorems re-proved: `etcd_txnlin_safe`, `etcd_compactwatch_safe`, `k8s_compactor_safe`,
    `k8s_compactor_partition_safe`, `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`,
    `k8s_etcd3_partition_safe`, and prophkv's results. The full list is regenerated with
    `etc/importers.py --uses` at the Draft.
- **7e:** `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe`.
  - Text unchanged.
  - Programs changed: list traffic, the history model, the gate switch, `Unknown` on unexpected
    seed revisions.
- **Changed interface files** (`interface/`, `etc/api/*` packages only):
  - none of client/v3, kubernetes or the etcd3 store is an API-listed package;
  - 7c-3 may change `interface/Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/{NewClient,NewClients,Writer}.txt`
    if `isNewClient`/`isKv` change;
  - 7e itself changes none. Each Draft regenerates and shows the diff.
- **New statements**: `Client.List.spec`, `GetList.spec`, the contract's list half, the driver's
  new functions' specs. `featureInit` is restated.
- **Changed statements** (addition 4): `ETooLarge` for Gets changes `store__Get.spec`. Its
  too-large outcome becomes recognizable (`storage.IsTooLargeResourceVersion` on the store's
  `NewTooLargeResourceVersionError`, told apart from the client's errors by 7c's T2(c)). The
  driver's `errOut`, `call` and `Apply` proofs follow.

**Vacuity.** Like every `_safe` theorem, these are vacuous until the `pbEnc_ok` per-type fix
lands. They rest on false axioms until sweep repairs 1, among them the `DefaultFeatureGate`
initializer that §4.1 restates jointly. 7e's results have their value once both land.

## 8. Go check (7e-0, before any Lean)

Under the 32G cap, each cluster test in its own process (`inChild`):
- `TestMainLinearizable`, `TestMainCluster` and `TestMainPartition` (five schedules) are `Ok`.
  `TestPartitionFailures`-style runs with forced failed writes also, with **porcupine's time and
  state count**: with `hist`, configurations stop merging.
  - If that blows up: keep `hist` only back to the smallest RV the traffic can still draw.
- **The model against upstream's `correctness.Model`**:
  - equality on consistent and latest-revision lists;
  - past-revision lists compared against an upstream `Model` rebuilt at `R` (they differ from
    upstream on purpose for `Exact`/`NotOlderThan`);
  - 7g's check is a refinement, not equality (§10).
- **A corrupted stale list** (an `Exact` list's items replaced by the store's at another revision)
  is rejected by porcupine. **A corrupted token** (wrong start key, or wrong RV) is rejected.
- **Selector with limit 1 whose last match is followed by a non-matching key** (has-more true,
  token present), and one with no keys after (has-more false).
- **`len(hist) = st.rv`** asserted after every model step in the model tests.
- The gate is off in `Main*`: a test reads `Enabled(EtcdRangeStream)` after the switch.
- Mode counts, as `TestTrafficReachesCases`:
  - every scope, recursion, match, limit and selector;
  - the past-revision modes;
  - `ETooLarge` lists (§1's RV deviation).

**Go pitfalls fixed in the design:**
- `hist` grows with full-slice appends (`append(c.hist[:len(c.hist):len(c.hist)], s)`) or an
  explicit copy, as `removeAt` copies `pend`, so configurations stepped from one parent never
  share a backing array;
- `isWrite` lists the write kinds explicitly, and `mstep` dispatches `KList` (a failed list is a
  failed read, not a pending write);
- `DecodeListItem` and `UpdateList` are written, not stubs.

## 9. Stages, checkpoints, estimate

Per stage, Lean lines (the review suggests 6000-9000 without streaming):

| Stage | Content | Estimate |
| --- | --- | --- |
| 7e-0 | Go: keys and `Obj` split, selectors, lists, `ETooLarge`, `hist`, gate switch, seed check; §8's tests | Go only |
| 7e-3a | pure `KModel`/`KSteps`: `hist`, `mlistL`, `stepL`; alongside 7e-0 | 600-900 |
| 7e-3b | the Go model's functions proved (as 6a), after 7e-0 | 1200-1800 |
| (7c-3) | its own landing: `Client.Get` at a revision, callers' glue | ~800 (7c's Scope) |
| 7e-1 | `Client.List` on 7c-3; after the per-type landing | 400-700 |
| 7e-2 | `GetList` path: trust specs (Draft), gate fact, `pagedChunks`, `appendChunk`, `finalizeList`, `listReadError`, the contract's list half, `DecodeListItem`/`UpdateList` | 2000-3000 |
| 7e-3c | `Refine`: `refine_list`, after 7e-2's Draft | 400-600 |
| 7e-4 | the driver: `Obj` codec and contract redone (namespace, node, app; D30g), `call`/`errOut` with lists and `ETooLarge`, `encIn`, `kInv`'s history from `stateAt` (seeds included), `InvSteps`, `Check`/`Main*`, adequacy, three closed theorems | 2000-3000 |
| total | without 7c-3 | 6600-10000 |
| 7s | streaming: `streamChunks`, `KV.GetStream`, the gate on; right after 7e | 1500-2500 |

**Checkpoints:**
1. 7e-0's Go report.
2. 7e-3a built.
3. 7e-1's statements.
4. 7e-2's Draft (statements, trust specs, gate fact: a hard stop).
5. 7e-3c.
6. 7e-4's Freeze package.

**Order**: 7e-0, with 7e-3a alongside, then 7e-3b. 7c-3 and 7e-1 come after the per-type landing.
7e-2's Draft follows 7e-1's statements, then 7e-3c, then 7e-4.

## 10. 7g

As 7d Scope §12, accepted in principle. The maintainers' `Model` and `Replay` run only on
histories with no failed write, chosen by a Go scan; our model checks the rest. 7g's check is a
**refinement**: on such runs, anything our model accepts, upstream's `Model` plus `Replay` accept.
It is not equality, since ours is stricter on latest-revision lists and checks past-revision
contents in-step.

## 11. Interaction with the work in flight

- **Per-type** (c9) rewrites `InvProto`/`InvGrpc`, which the client chain sits on. 7c-3 and 7e-1
  wait for its landing.
- **Sweep repairs 1** repairs the `DefaultFeatureGate`/`DefaultFeatureSupportChecker` initializers
  that §4.1 restates. One joint restatement, coordinated through 81. Otherwise it does not touch
  the client or the store.
- 7e-0 (Go) and 7e-3a (pure) are independent of both and start first.

## 12. Questions left for 81

None: Q7e-1..5 are decided above, and `ETooLarge` for Gets too (81, 2026-11-08).
