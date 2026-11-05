---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: no
---

# k8s apiserver etcd3: `StartCompactorPerEndpoint` can keep a stopped compactor if the client's endpoints change

`StartCompactorPerEndpoint` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go:52`) registers the new
compactor under each of `client.Endpoints()` in the package's `endpointsMap`, and its `onClose`
(run by `Stop`) deletes the entries of `client.Endpoints()` *as they are when `Stop` runs*. If the
client's endpoints changed in between (`Client.SetEndpoints`, or `autoSync` with
`Config.AutoSyncInterval`), the entries of the endpoints it no longer has stay, pointing to the
stopped compactor. A later `StartCompactorPerEndpoint` whose client has one of them returns that
stopped compactor, so that process never compacts again.

**Why not an issue:** a precondition Kubernetes meets. The only caller,
`storagebackend/factory/etcd3.go`'s `startCompactorOnce`, passes a client built by `newETCD3Client`,
which sets no `AutoSyncInterval` and on which nothing calls `SetEndpoints` (searched the factory,
2026-11-05), so its endpoints never change. Upstream not searched. Found by code reading while
surveying Q1 (c) of `notes/k8s-compactor-plan.md`.

## Proof

no: a spec of `StartCompactorPerEndpoint` would take the client's endpoints as fixed (the client's
`Endpoints` spec returns the read-only field's value).
