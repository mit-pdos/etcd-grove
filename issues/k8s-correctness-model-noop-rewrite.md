---
upstream: none
checked: 2026-10-26
links:
  - kubernetes/kubernetes#141652 issue open: the tracking issue of the model-based correctness tests; lists "No-op update" as covered, nothing on stale or non-canonical stored data
  - kubernetes/kubernetes#141729 pr merged: added `correctness.Model`
  - kubernetes/kubernetes#142089 pr merged: added updates to the Model, with the no-op check this finding is about
  - kubernetes/kubernetes#143303 pr merged: transformer variants of the correctness tests (its transformer is never stale and the test writes all the data, so the case is still not reached)
  - kubernetes/kubernetes#48394 pr merged: the store's rule (`GuaranteedUpdate` writes when the stored data is not canonical) the Model does not follow
  - kubernetes/kubernetes#143129 pr open: touches `model.go` (NotFound tolerance), not the no-op path; related, different (also #143131, #143153, the same change)
---

# k8s correctness.Model: a no-op update of non-canonical or stale stored data is rejected, but the etcd3 store rewrites it by design

- **Status**: a bug in Kubernetes' storage test model (`correctness.Model`), not in the store. In
  this case the Model is stricter than the store it specifies: it rejects a response that the
  store's own unit test (`RunTestGuaranteedUpdateChecksStoredData`) requires. `TestCorrectness`
  never reaches the case, because there every stored value is written by the store with the
  test's codec and identity transformer. A run that starts from data written in another
  encoding (`NewModelFromStorage` builds the Model from such a store), or with a transformer
  that reports `stale` (an encryption key rotation), would fail the linearizability check on a
  correct store. Closer since: the integration `TestCorrectness`
  (`test/integration/apiserver/storage/correctness_test.go:344`) now seeds its Model from a store
  listing (`NewModelFromStorage`), and since kubernetes/kubernetes#143303 (merged 2026-10-22) runs
  transformer variants; their `prefixTransformer` never reports `stale` and the test writes all the
  data, so the case is still not reached (rechecked at master `765dd1d`, 2026-10-26: `store.go:573`,
  `model.go:325-337`).
- **Where** (kubernetes master `d9cafe4`, `staging/src/k8s.io/apiserver/pkg/storage/`):
  - `etcd3/store.go:547` (`GuaranteedUpdate`): the write is skipped only when
    `!origState.stale && bytes.Equal(data, origState.data)`. The new encoding must be
    byte-equal to the stored one, and the stored one must not be stale (the fix of #48394, so
    that such data gets rewritten).
  - `testing/correctness/model.go`, `Model.update`: the write is skipped when the stored and
    updated objects are `reflect.DeepEqual` without their resource version. A model item is an
    object and does not record its stored bytes or staleness.
- **What happens**: the object is stored in a form the codec no longer writes (here a leading
  space after the transformer's prefix, as `RunTestGuaranteedUpdateChecksStoredData` seeds it),
  or the transformer reports it stale. A `GuaranteedUpdate` whose `tryUpdate` returns its input
  unchanged then writes, and returns the object at a new resource version (2 -> 3).
  `Model.Step` expects the stored object at the old resource version and returns `ok = false`.
  Reproduction: `k8s-correctness-model-noop-rewrite/model_noncanonical_test.go`, a test of package
  `etcd3`, both cases. Run it in a writable copy of the published `k8s.io/apiserver`
  `v0.0.0-20261021221356-9c4ec15b8038` (kubernetes master of 2026-10-21) with
  `GOWORK=off GOFLAGS=-mod=mod go test ./pkg/storage/etcd3/ -run TestModelRejectsRewriteOfNonCanonicalData -v`.
  Both subtests pass, which means the Model rejected the response (2026-10-22, upstream etcd
  v3.7.2).
- **Expected**: the Model documents itself as "a state machine that mimics kubernetes storage
  behavior". For that, an update of an item whose stored form differs from what the codec
  writes now, or is stale, should write (bump the resource version) even when the object is
  unchanged.
- **How the proof handles it**: the generic specs of the store (planned,
  `notes/k8s-etcd3-plan.md`) describe the store's rule, not the Model's. The Lean model's item
  carries whether its stored value is the codec's current encoding and not stale, and when every
  item is canonical it coincides with `correctness.Model`. The closed driver theorem (planned) checks against a fixed
  copy of the Model in `examples/k8setcd3/`, trusted until upstream fixes it, so that its
  non-canonical codec can be checked (`notes/decisions.md`, D30g).
- **Possible fixes**: let the Model know whether an item needs a rewrite. For example, a
  `Model.Items` entry could record the item's encoding (or a "stale" bit set by a seeding
  helper), and `update` could compare encodings as the store does. Or document that the Model
  assumes every stored value is canonical and not stale, and have `NewModelFromStorage` check
  that it lists only such data.
- **Found**: 2026-10-22, planning the generic specs of the Kubernetes etcd3 store against
  `correctness.Model` (`notes/k8s-etcd3-plan.md`, the codec contract).
