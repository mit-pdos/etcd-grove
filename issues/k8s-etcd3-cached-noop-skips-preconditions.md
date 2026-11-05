---
upstream: none
checked: 2026-11-05
links:
  - kubernetes/kubernetes#82303 pr closed: related, not this bug (preconditions retried with the live object when they fail on cached data; this bug is when they pass on it)
  - kubernetes/kubernetes#89828 pr closed: related (introduced the cached object for Delete)
blocks-proof: yes
---

# apiserver etcd3: GuaranteedUpdate from a cached object that changes nothing ignores a failed resource version precondition

An update through the etcd3 storage that changes nothing, started from a cached object (as the
watch cache supplies for every update), succeeds and returns the current object even when its
resource version precondition names an older version, if etcd meanwhile holds the same contents at
a newer resource version. The precondition, and the update function, were checked only against the
cached object. When the newer stored value is due for a rewrite (an encryption key rotation), the
store also writes it, still without checking the precondition against it.

**Expected:** `GuaranteedUpdate` should return an `InvalidObj` error when the preconditions fail on
the object stored in etcd, as it does without a cached object: the cached object "can be used as a
suggestion about the current version of the object", and "the implementations have to retry in
case suggestion is stale"
([`interfaces.go`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/interfaces.go#L228-L230)).

**Impact:** an update whose result equals the object, carrying a resource version precondition
(a delete's `preconditions.resourceVersion`, through `updateForGracefulDeletionAndFinalizers`) or a
resource version check in `tryUpdate` (the registry's `Update` compares the request's
`resourceVersion` with the object `tryUpdate` is given), with the watch cache's object as the
suggestion (`CacheDelegator.GuaranteedUpdate` passes it whenever the preconditions pass on it). It
needs etcd to hold the same bytes at a newer resource version than the suggestion: a rewrite with
equal contents (storage version migration's no-op updates of objects stored in an older encoding,
re-encryption after a key rotation), or a delete and re-create of the same object. The request
then succeeds with the newer version instead of failing with a conflict. No data is lost when the
contents are equal; optimistic concurrency is not enforced. Low impact.

**Reproduction:** `TestGuaranteedUpdateCachedNoopChecksPreconditions` in
[`issues/k8s-etcd3-cached-noop-skips-preconditions/cached_noop_test.go`](k8s-etcd3-cached-noop-skips-preconditions/cached_noop_test.go),
copied into `pkg/storage/etcd3` of a writable copy of
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (kubernetes/apiserver@9c4ec15b8038, the
pin of `examples/k8s/etcd3/go.mod`, 2026-10-21), go1.27.1 linux/amd64:

```
$ go test ./pkg/storage/etcd3 -run TestGuaranteedUpdateCachedNoopChecksPreconditions -count=1
--- FAIL: TestGuaranteedUpdateCachedNoopChecksPreconditions (1.03s)
    cached_noop_test.go:42: precondition ResourceVersion=2 on an object at ResourceVersion=4: expected an InvalidObj error, got err=<nil> and the object at ResourceVersion="4"
FAIL
```

The test creates a pod (resource version 2, kept as the cached object), deletes it and creates it
again with the same contents (resource version 4), then calls `GuaranteedUpdate` with a no-op
update function, the precondition `ResourceVersion: "2"` and the cached object. Without the cached
object the same call returns `InvalidObj`.

**Cause:** `GuaranteedUpdate` checks the preconditions and calls `tryUpdate` on the cached object's
state ([`store.go#L527-L544`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/store.go#L527-L544)).
When the result's encoding equals the cached object's, it re-reads the key and restarts the loop
only if the bytes differ
([L556-L564](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/store.go#L556-L564));
with equal bytes it returns the re-read object, or writes it if stale
([L566-L575](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/store.go#L566-L575)),
although the re-read state's resource version may differ from the one the preconditions and
`tryUpdate` saw.

## Proof

yes: the k8setcd3 driver's traffic (`examples/k8s/etcd3`) reached it (`cachednoop_test.go` there,
after the no-op rewrite of a key seeded in an older encoding); stage 7b excludes it by a scope
premise: an update with a cached object carries no resource version precondition
(`genFrom`; `notes/k8s-etcd3-plan.md`, "7b: Draft, the cached no-op").

## Fix

Restart the loop after the re-read unless its resource version is the cached one, so the
preconditions and `tryUpdate` run on the current object: `fix.patch` (against
`staging/src/k8s.io/apiserver`; with it the test passes, and so do the package's
`TestGuaranteedUpdate*` tests). No fix branch yet.

## Notes

Found 2026-11-05 designing the proof of `GuaranteedUpdate` with a cached object (stage 7b of
`notes/k8s-etcd3-plan.md`). Related but different: `nonissues/k8s-etcd3-cached-object-trusted-at-current-rv.md`
(a cached object that etcd never held at its resource version).
