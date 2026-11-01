---
upstream: unchecked
checked: 2026-11-01
links: []
---

# The etcd3 store trusts a cached object whose resource version is current

**Status**: an unstated precondition (documentation). `storage.Interface` calls
`cachedExistingObject` a suggestion that implementations "have to retry in case suggestion is
stale"; the etcd3 store detects staleness by resource version only, so a cached object at the
key's current resource version is taken as the stored object, whatever its contents. A caller
must pass an unmodified copy of what storage returned at that resource version; the interface does
not say so.

**Where** (`k8s.io/apiserver` at the pin of `examples/k8setcd3/go.mod`, `v0.0.0-20261021221356-9c4ec15b8038`):
- `pkg/storage/interfaces.go:187-189` (`Delete`) and `:228-230` (`GuaranteedUpdate`): the
  documentation of `cachedExistingObject`.
- `pkg/storage/etcd3/store.go:429-430` (`conditionalDelete`): `getStateFromObject(cached, false)`
  encodes the cached object as `origState.data`, its resource version as `origState.rev`.
- `store.go:467-490` (`deleteOnce`): `OptimisticDelete(key, origState.rev)` succeeds when the
  key's mod revision is `origState.rev`, and `out` is decoded from `origState.data`, the cached
  object's encoding, not from what etcd held.
- `GuaranteedUpdate` the same way (`store.go:494-587`): `tryUpdate` runs on the cached object, and
  the write's compare is on its resource version only.

**What happens**: a caller passing a cached object `o_c` with resource version `r`, where etcd
holds a different object `o_s` at mod revision `r` (a copy modified after it was read, or an object
of another key at the same revision): `Delete` deletes the key and returns `o_c` as the deleted
object; `GuaranteedUpdate` writes `tryUpdate(o_c)`, losing `o_s`'s contents, with no conflict. The
validation callbacks (`validateDeletion`, preconditions) run on `o_c` too. No reproduction yet (it
needs an etcd member; the scenario is a few lines over `TestCorrectness`'s setup).

**Expected**: either the documentation states that a cached object must be one the storage
returned (unmodified) for that key at its resource version, or the store treats it only as a
suggestion of the resource version and re-reads the data (which defeats its purpose: avoiding the
read).

**How the proof handles it**: found while designing the specs of `Delete`/`GuaranteedUpdate` with a
cached object (`notes/k8s-etcd3-plan.md`, stage 7b): the specs take, for a cached object, a witness
that the key held it at its resource version (a fact of an earlier answer of the store), not any
object. The current specs fix the cached object to `nil` (`Spec/k8s_io/apiserver/pkg/storage/etcd3/
store__Delete.lean`, `store__GuaranteedUpdate.lean`).

**Possible fixes**: one sentence in `interfaces.go` for both methods ("`cachedExistingObject`, when
non-nil, must be an unmodified object previously returned by this storage for `key`"). Kubernetes'
callers (the registry's `Store.Delete`/`Update` passing the watch cache's object) already meet it;
`TestCorrectness`'s traffic does (`traffic.go`: the cached object is a previous response).

**Found**: 2026-11-01, by the spec review of the etcd3 store's specs (stage 7b's design).
