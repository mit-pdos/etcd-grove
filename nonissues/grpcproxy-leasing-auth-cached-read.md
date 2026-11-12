---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# grpcproxy: with `--experimental-leasing-prefix` and auth, a cached key is served to a user without read permission

The gRPC proxy sends each request with its requester's token, but the leasing KV's cache is shared
by all of them and answers a cached `Get` without contacting a member: a user without read
permission on a key gets its value once another user's `Get` cached it; the watch proxy's
permission check (a range read through the same KV) passes for such a user too.

**Why not an issue:** suspected from code reading (the completeness review of batch 1e), not run;
needs a non-default flag on a best-effort component, so configuration hardening under etcd's
threat model, not a security report; the proxy's own range cache already serves serializable reads
across principals. Code: [`leaseCache.Get`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/cache.go) (no permission check).

## Proof

no: W0's model lets a serializable read skip the permission check, which is what a cached answer
is stated as (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`, `CachedSer`).
