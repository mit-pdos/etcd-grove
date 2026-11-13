# k8s etcd3 stage 7e, lists: Scope (draft, 2026-11-07, branch `k8s-7d`; to etcd-grove-81 for review)

The stage in `notes/k8s-etcd3-plan.md`, "Phase 7", 7e: `store.GetList` (the paginated path,
`EtcdRangeStream` off) under `TestCorrectness`'s list traffic, with the stale-list design (b) of
`notes/k8s-7d-scope.md` §2, which 81 leans to. No Lean until 81 approves. The pins are 7d's:
`k8s.io/kubernetes` `878cfa6c4cc7`, `k8s.io/apiserver` `9c4ec15b8038`, etcd fork `673da07c8f`.

## 1. The traffic the test sends (`correctness_test.go:84-125`, `traffic.go:376-418`)

Lists are 25% of the unary operations. Each list draws:
- **a scope**: cluster `/pods/` (50%), namespace `/pods/<ns>` (25%), object `/pods/<ns>/<name>`
  (25%). Then **`Recursive` is drawn again** (true 70%, false 30%) and overrides the scope's own.
  So a non-recursive "cluster" list reads the one key `/pods/` (absent), and a recursive "object"
  list is a prefix list of `/pods/<ns>/<name>/`;
- **a field selector**: everything 25%, by name 15%, by namespace 15%, by node 20%, by empty node
  15%, combined 10%; **a label selector**: everything 60%, by app 40% (`pickPredicate`, on Pods);
- **a resource version** as for Gets (empty 30, `0` 15, `1` 10, cached 15, current 14, past 14,
  future 2). With a non-empty RV, **a match**: `""` 50%, `NotOlderThan` 25%, `Exact` 25%
  (`Exact` with RV `0` is dropped: `return nil`);
- **a limit** (only when RV ≠ `"0"`): 0 70%, 1 15%, 2 15%. It never sets `Predicate.Continue`.

The test's objects are four, chosen to test prefix boundaries: `ns-1/pod-1`, `ns-1/pod-11`,
`ns-2/pod-2`, `ns-11/pod-1`. So `/pods/ns-1` must not list `ns-11`, and `pod-1` must not list
`pod-11` (`keyInScope`; the bug class of #94002).

## 2. Which lists are stale in the etcd3 store

`storage.ValidateListOptions` (`interfaces.go:372`) and `GetList`/`pagedChunks` (`store.go:763-905`)
decide the revision read:
- **at the latest revision** (`withRev = 0`, then fixed to the first page's revision for later
  pages): no RV, RV `"0"`, `NotOlderThan` (then `validateMinimumResourceVersion` against the read
  revision: too-large if above), and legacy `""` without a limit or with RV `0`. These answers are
  the state at the first page's read. They are linearizable, and the driver's model checks them
  exactly, as it checks Gets (upstream checks only `NotOlderThan`'s resource version);
- **at a past revision** (`withRev = RV`): `Exact`, and legacy `""` with `Recursive`, `Limit > 0`,
  `RV > 0`. These are the stale reads. A requested revision above the current one gives
  `ErrFutureRev`, which `listReadError` maps to `TooLargeResourceVersion` (after a
  `GetCurrentResourceVersion` call). A revision below the compaction revision gives
  `ErrCompacted` → 410. **The driver has no compactor**, so 410 is unreachable and compaction is
  out of this stage.

## 3. The design: the history in the model (7d Scope §2 (b))

**The driver's model** (`k8setcd3.go`, the Go copy of `correctness.Model`, D30m):
- a configuration (`mcfg`) gains **its stores by revision**: `hist []mstore`, the store after each
  revision since the seeded base. A write that takes effect appends its result. The pending
  failed writes keep their place: a configuration where one took effect has its revision in its
  history;
- `mlist(in, c)` is `Model.list` on the configuration:
  - at the latest revision for the modes of §2's first bullet, from `c.st`;
  - at `in.RV` for the past-revision modes, from `c.hist[RV]`: the items in scope, sorted, filtered
    by the predicate, the first `limit` matching ones, "has more", the remaining count, and the
    list's resource version (the requested RV for a past read, the store's for a latest read);
  - too-large above the store's revision;
- **the step for a list compares the whole answer**, past revision included. So porcupine itself
  rejects a stale list whose contents are not the store's at that revision, and **no replay is
  needed for soundness**. In every run, failed writes included, the real linearization keeps the
  real history, and porcupine is complete. This is why (b) and not (a) (7d Scope §2);
- `Equal` compares the histories. They grow by one store per write: `4 × 60` operations is a few
  hundred stores per configuration. A Go test measures porcupine's time with the heavier `Equal`.

**The output** (`Output`) gains the list's items (name, UID, value, RV), the list RV, `HasMore` and
`RemainingItemCount`. **The continue token is compared by presence**, not by its bytes.
Upstream's `equalListResponse` compares the token that `storage.PrepareContinueToken` builds
(JSON in base64): copying that into the model needs `encoding/json`'s and `encoding/base64`'s
specs. Comparing the token itself is left to 7g (the maintainers' `Model` with D30g's patch)
(**Q7e-1**).

**Selectors** (**Q7e-2**). The driver's `Obj` has a name, a UID and a value; the test's predicates
are on Pods (namespace, name, node, app label).
- Recommended: give `Obj` a namespace (from the key) and a node (a second value field, drawn as
  the test draws `Spec.NodeName`), with `GetAttrs` returning the fields `metadata.name`,
  `metadata.namespace` and `spec.nodeName`, and the label set empty or `app`. The traffic then
  draws the test's six field selectors and two label selectors;
- `SelectionPredicate.Matches` calls apimachinery's `labels.Selector.Matches` and
  `fields.Selector.Matches`, names-only today. These need trust-boundary specs for the selectors
  the driver builds (`fields.OneTermEqualSelector`, `AndSelectors`, `labels.SelectorFromSet`,
  `Everything`), or a translation of those apimachinery packages;
- the cheaper first step is `Everything` and by-name only. Then the predicate is the driver's own
  `GetAttrs` and one equality.

**The keys** (**Q7e-3**). Adopt the test's four objects in two-level keys `ns/name`, so that
namespace scope and the prefix boundaries are exercised. This changes `workloadKeys`, the seeds
(two of the four) and `Gen`. The proofs see the keys only as strings, so the change is
mechanical.

## 4. The store side (Go code that is not ours)

The path and what each piece needs:
- `store.GetList` (`store.go:763`), translated in 7a: `prepareKey` (proved), `meta.GetItemsPtr` and
  `conversion.EnforcePtr` of the list. These are `reflect`: local trust-boundary specs like the
  store's other `reflect` axioms (D30l);
- `storage.ValidateListOptions` (`interfaces.go:372`): `DecodeContinue` is unreachable (no continue
  token is sent); `ParseResourceVersion` is the driver's versioner (proved);
- `pagedChunks`: a range over an `iter.Seq2` with a `yield` closure (G2, Perennial `caa9d07ee`);
  `getList` → `kubernetes.Client.List` (§5); page doubling (`limit *= 2` up to `maxLimit`);
- `appendChunk`/`processListItem`: `decoder.DecodeListItem` (the driver's, proved:
  `decodeObj`), `SelectionPredicate.Matches` (§3), and `reflect`'s slice operations (`Append`,
  `Len`, `Value.Set`) on the list's items. These are local trust-boundary specs;
- `storage.PrepareContinueToken`: `EncodeContinue` (`encoding/json` + `base64`; names-only today),
  reached only when `hasMore`. Trust-boundary specs: some string, deterministic in its inputs;
- `finalizeList`: `versioner.UpdateList`, so the contract (`contractOk`, D30g) grows a list half,
  proved for the driver's versioner; `aggregator.Err()`;
- `listReadError`: `errors.Is(err, ErrFutureRev)` is 7c's error identity, then
  `GetCurrentResourceVersion` (`store.go`: a `kubernetes.Client` read; its spec is new) and
  `NewTooLargeResourceVersionError`; `interpretListError`: the `ErrCompacted` branch is
  unreachable, and any other error stays the client's.

The store's spec for `GetList` is logically atomic, against the store's model `KSt`
(`Model.lean`) extended with the history (§6): the answer is `mlist` at one linearization point,
for the first page's read. Later pages read at the same revision, so the whole answer is that one
revision's.

## 5. The client: `kubernetes.Client.List` at a revision (needs 7c-3)

Q7e was approved in 7c's Scope as (a): as `Client.Get`'s spec, with a prophecy patch for the
response's revision. Its answer is the keys of `[start, prefixEnd)` at the revision read, sorted,
the first `limit`; `Count` is the number of keys in that range; `Revision` is the header's (the
*current* revision, also for a past read: `TestReadAtRevision`). Its errors are as `Get`'s, with
7c's soundness for `ErrFutureRev`/`ErrCompacted`.

**Prerequisite: 7c-3**, the client chain at a revision. `Client.Get` is still latest-only
(`Spec/.../kubernetes/Client__Get.lean`: "the only revision the server's specs serve"). The
server side is done: M2's `txn.executeRange` gives `stateAt` of the read log, `ErrFutureRev` or
`ErrCompacted`, and 7c-2 gives the gRPC error outcome. 7c-3 carries this through linkvtxn's
`client_*` specs to `KV.Get` with `WithRev`/`WithRange`/`WithLimit`. **7e-1 below is 7c-3 plus
`List`.**

## 6. The model in Lean and the invariant

- `KModel.lean`: `mcfg`'s Lean record gains `hist`; `mlistL` (the pure list: scope by prefix with
  the `/` boundary, sort, predicate, limit, has-more, remaining count); `stepL` compares lists;
  `PendSpec`'s pending writes append to the history when they take effect;
- `Refine.lean`: `KRel` relates the store's `KSt` to a configuration's `st`, and now the store's
  history to `hist`. `refine_list` relates `GetList`'s spec answer to `mlistL`;
- the driver's invariant (`Inv.lean`, `kInv`): for the configuration that matches etcd,
  `hist[R] = absK (stateAt R)` for every revision `R` from the seeded base to the current one. The
  server's read log (M2) is the source, and each write that takes effect appends (a new conjunct
  of `kInv`; the commits in `InvSteps.lean` extend it);
- the seeded base: revision 1 is the empty store, 2 and 3 the seeds. `Exact` at RV `1` lists the
  empty store.

## 7. Premises, trust base, closed theorems

- **New trust-boundary axioms** (estimate 10-16, each attacked by the `axiom` skill in the round
  that writes it):
  - `reflect`'s slice operations on the list;
  - `meta.GetItemsPtr`/`meta.SetList`, `PrepareContinueToken`'s encoding;
  - the selectors' `Matches` (Q7e-2);
  - `GetCurrentResourceVersion`'s client read, if not proved from `Client.List`'s spec.
- **Closed theorems**: `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe`
  keep their text. Their programs gain list traffic and the history model. Their premises gain
  only what §4's axioms add, so the `k8setcd3` collection grows.
- **Trusted text**: the driver's model grows by `mlist` and the history (the Go copy, D30m),
  until 7g.
- **Store and client specs**: `GetList.spec`, `Client.List.spec`, `Client.Get.spec` at a revision
  (7c-3), the contract's list half. Each change is old → new in the Draft.

## 8. Go check (before any Lean)

Run the driver with lists under the 32G cap, each cluster test in its own process (`inChild`):
- `TestMainLinearizable`, `TestMainCluster`, `TestMainPartition` (five schedules) `Ok`;
- the model against the real `correctness.Model` on random list traffic from canonical states
  (as `TestModelMatchesCorrectnessModel`), up to the continue token's bytes;
- **a corrupted stale list** (an `Exact` list's items replaced by the store's at another
  revision) is rejected by porcupine;
- porcupine's time with the history in `Equal`, at the test's 8 × 1250 scale and at the theorem's
  sizes;
- the counts of each mode reached (the stale modes in particular), as `TestTrafficReachesCases`.

## 9. Stages and estimate

1. **7e-0, Go**: the driver's lists, keys, selectors, `Output`, and the history model; the Go
   tests of §8. Checkpoint: the Go report.
2. **7e-1, the client at a revision** (7c-3 and `Client.List`): statements first (Draft), then
   proofs. Hub: `client_*` specs (coordinate with the hub owner).
3. **7e-2, the store's `GetList`**: trust-boundary specs (Draft), `pagedChunks`,
   `appendChunk`/`processListItem`, `finalizeList`, `listReadError`; the contract's list half.
4. **7e-3, the model**: `KModel`/`KSteps` with `hist` and `mlistL`, the Go model's functions proved
   (as 6a), `Refine` (as 6b).
5. **7e-4, the driver**: `call` with lists, `errOut`, `Apply`, the invariant's history,
   `Check`/`Main*`, adequacy, the closed theorems rebuilt. Freeze.

Estimate: the largest stage after 7f. Roughly 4000-6000 lines of Lean, two to three agent-weeks,
dominated by 7e-2 (`reflect`, `iter.Seq2`, the paging loop) and 7e-1 (the client chain at a
revision).

## 10. 7g (from 7d Scope §12)

With (b), 7g runs the maintainers' `Model` and `Replay` only on runs with no failed write. There
they are sound (7d Scope §12), and the driver's model checks the rest. 7e's model keeps the
maintainers' list semantics, so 7g's comparison of the two on runs without failed writes is a Go
test plus the translation.

## 11. Interaction with the work in flight

- c9's per-type branch rewrites `InvProto`/`InvGrpc`, which the client's specs sit on. 7e-1
  touches the client chain (`client_*`), so 7e-1 waits for the per-type landing or coordinates
  with it.
- Sweep repairs 1 does not touch the client or the store.
- 7e-0 (Go) and 7e-3 (pure model) are independent of both and can start now.

## 12. Questions for 81

- **Q7e-1.** The continue token compared by presence (recommended), or by its bytes (copies
  `PrepareContinueToken`'s JSON/base64 into the model: two more trust-boundary specs).
- **Q7e-2.** Selectors: `Everything` and by-name first (recommended for 7e), the test's full six
  field and two label selectors in a follow-up, with apimachinery's selector specs.
- **Q7e-3.** The test's four two-level keys (recommended), replacing `a`, `b`, `c`.
- **Q7e-4.** Order: 7e-0 and 7e-3 now. 7e-1 after the per-type landing (it touches the client
  chain). 7e-2 after 7e-1's statements.
