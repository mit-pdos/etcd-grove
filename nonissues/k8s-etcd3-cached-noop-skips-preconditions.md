---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: yes
---

# etcd3 store: an update from a cached object that changes nothing skips the preconditions when the object was rewritten

`GuaranteedUpdate` of `k8s.io/apiserver`'s etcd3 store, given a cached object and preconditions,
answers success with the key's current object when the update leaves the cached object unchanged
and etcd holds the same bytes at a newer resource version: the preconditions (and `tryUpdate`) ran
only on the cached object, so a resource version precondition naming the cached object's version
passes although the stored object's version differs. If the re-read value is stale (the
transformer asks for a rewrite), the store also writes the cached object's update over the newer
version, still without checking the preconditions on it.

**Why not an issue:** the failing scenario is a test in this repository's driver
(`examples/k8s/etcd3/cachednoop_test.go`, `TestCachedNoopPrecondition`, against an etcd member),
not yet in the store's own harness (`pkg/storage/etcd3/store_test.go`); Kubernetes'
`TestCorrectness` traffic reaches it rarely if at all (its items are always written in the current
encoding, so equal bytes at a new revision need a delete and a re-create of the same object, with
the same UID: an `ignoreNotFound` update re-creating it, then a cached update from the deleted one).

## Proof

yes: the k8setcd3 driver's traffic reaches it (a cached object with a resource version precondition
on an update, after a non-canonical seed's rewrite or a re-create of the same object), and the
store's answer is not the model's; stage 7b decides (`notes/k8s-etcd3-plan.md`, "7b: Draft, the
cached no-op").

## Notes

**Where** (`k8s.io/apiserver` at the pin of `examples/k8s/etcd3/go.mod`,
`v0.0.0-20261021221356-9c4ec15b8038`), `pkg/storage/etcd3/store.go`, `GuaranteedUpdate`:
`preconditions.Check` and `updateState` (`tryUpdate`) run on `origState`, the cached object's
state (`getStateFromObject`, `current = false`). At `:552`, when `tryUpdate`'s encoding equals
`origState.data`, `:556-564` re-read the key (`getCurrentState`) and continue only if the data
changed; when the bytes are equal, `:566-572` decode the re-read state into `destination` and
return `nil`, and when it is stale fall through to `updateOnce` with the re-read state's revision
and the old `data`. Neither path re-runs the preconditions or `tryUpdate` on the re-read state,
whose revision may differ from the cached one.

**Reproduction** (the driver's test, its model a copy of `correctness.Model`, which the real Model
agrees with): seed `a` in an older encoding at revision 2; `Get(a)` (cached: `a` at `2`); a no-op
`GuaranteedUpdate(a)` rewrites it in the current encoding at `4`; then
`GuaranteedUpdate(a, preconditions{ResourceVersion: "2"}, tryUpdate = no-op, cached = a@2)` returns
`a` at `4`, no error. `correctness.Model` answers `InvalidObj` (the precondition fails on the
stored object at `4`).

**Impact**: an update that carries a resource version precondition (the registry's `Update` passes
the request's `metadata.resourceVersion` as one) and a cached object from the watch cache succeeds
with a newer version instead of a conflict, after a rewrite with equal bytes: storage version
migration's no-op updates, or a re-encryption, rewrite every object with equal plaintext. With a
stale value (key rotation), the store writes without the precondition holding.

**Possible fix**: after the re-read at `:557`, continue the loop (re-running the preconditions
and `tryUpdate`) unless the re-read state's revision is the cached one, as `refreshOnError` does.

**Found**: 2026-11-05, designing stage 7b's `GuaranteedUpdate` spec with a cached object.
