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
blocks-proof: no
---

# k8s correctness.Model rejects the etcd3 store's rewrite of non-canonical or stale data on a no-op update

Kubernetes' storage test model (`apiserver/pkg/storage/testing/correctness`, `Model.update`)
skips every update that leaves the object unchanged, but the etcd3 store's `GuaranteedUpdate`
deliberately writes (and bumps the resource version) when the stored bytes are not the codec's
current encoding or the transformer reports them stale (#48394). On such data the Model rejects a
correct store's response.

**Why not an issue:** a test helper, and no test reaches the case: `TestCorrectness` writes all its
data with the test's codec and an identity or never-stale transformer, so every stored value is
canonical (rechecked at master `765dd1d`, 2026-10-26).

## Proof

no: the store's rule is what the proof states; the Lean model's item carries whether its stored
value is canonical and coincides with `correctness.Model` when every item is
(`Proof/k8s_io/apiserver/pkg/storage/etcd3/Model.lean`, `KSt.update_eq_updateM`), and the driver
checks against a fixed copy of the Model (`examples/k8setcd3/`; `notes/decisions.md`, D30g).

## Notes

Test: [`k8s-correctness-model-noop-rewrite/model_noncanonical_test.go`](k8s-correctness-model-noop-rewrite/model_noncanonical_test.go)
(package `etcd3`), run 2026-11-01 in a writable copy of `k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`
(master of 2026-10-21) with `GOWORK=off GOFLAGS=-mod=mod go test ./pkg/storage/etcd3/ -run
TestModelRejectsRewriteOfNonCanonicalData -v`: it passes, which shows the bug (`store rewrote the
object: RV 2 -> 3`, `correctness.Model rejects the store's response`, both subtests). A test that
failed would have to assert the Model accepts the response. It would matter if the integration
`TestCorrectness`, which seeds the Model from storage (`NewModelFromStorage`), ever starts from data
in an older encoding or rotates an encryption key. Fix: let a Model item record whether it needs a
rewrite, or document that the Model assumes canonical, non-stale data.
