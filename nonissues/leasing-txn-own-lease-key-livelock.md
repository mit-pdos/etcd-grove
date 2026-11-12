---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: no
---
# clientv3/leasing: a transaction may retry forever on the client's own lease key after an error

After a leasing transaction fails with an error, its compared keys are evicted from the cache but
their lease keys, with this client's lease, stay. A later write transaction on such a key guards
`CreateRevision(pfx+k) < 1`, which fails; its fallback reads the lease key, which `revokeLeaseKvs`
skips as its own; nothing changes, and `serverTxn` resends the same transaction until its context
ends: forever, as a busy loop of requests, with a context that has no deadline.

**Why not an issue:** found by code reading (the provability review of batch 1e); no test run.
A liveness bug. Code: [`serverTxn`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/txn.go), [`guardKeys`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/txn.go),
[`revokeLeaseKvs`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go).

## Proof

no: liveness (the specs are partial).
