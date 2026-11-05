---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: no
---

# k8s apiserver: two transports with a common endpoint share one compactor, and either's last user stops it

`startCompactorOnce` (`k8s.io/apiserver/pkg/storage/storagebackend/factory/etcd3.go:407`) keeps one
compactor per transport configuration (`key := fmt.Sprintf("%v", c)`: the servers *and* the TLS
files), refcounted, and stops it (`compactor.cancel()`, which is `c.Stop`) when the key's count
reaches zero. But the compactor comes from `etcd3.StartCompactorPerEndpoint`, which returns the
compactor already registered for any of the client's endpoints. So two transport configurations
that differ (other TLS files, or a server list in another order) and share an endpoint share one
compactor, each counting it separately: when the first key's count reaches zero, it stops the
compactor the second key still uses, and the second key's storage is no longer compacted (no panic:
`CompactRevision` keeps returning the last revision). Likewise, the "replace if the interval got
smaller" branch stops the old compactor and asks `StartCompactorPerEndpoint` for a new one, which may
return another key's compactor at its larger interval.

**Why not an issue:** a precondition Kubernetes' configurations meet in practice, and no failure the
code reports. An API server's resources share one transport configuration unless overridden per
resource (`--etcd-servers-overrides`), and an override names other servers, with the default TLS
files: two configurations with a common endpoint and different keys do not arise from the flags.
Upstream not searched. Found by code reading (the spec review of `StartCompactorPerEndpoint`, Q1 (c)
of `notes/k8s-compactor-plan.md`).

## Proof

no: `StartCompactorPerEndpoint`'s spec returns a compactor of the caller's cluster, which may be
another caller's and may be stopped by it; `Stop` and `CompactRevision` are safe on a stopped
compactor (`isCompactor` is persistent).
