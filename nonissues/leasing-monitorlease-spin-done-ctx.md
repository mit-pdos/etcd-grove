---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: no
---
# clientv3/leasing: a lease monitor spins when its watch ends before a revoke

A lease monitor re-reads its lease key with the context of the `Get` that started it and retries on
error in a loop bounded only by the leasing KV's context. Once that `Get`'s context is done (the
proxy's per-request contexts always are by then) and the monitor's watch has ended without a
`"REVOKE"` (a canceled watch, a compacted start revision), every read fails at once and the loop
spins at full CPU until the leasing KV is closed.

**Why not an issue:** found by code reading (the provability review of batch 1e); how often the
watch ends early is not established; no test. Code: [`monitorLease`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go).

## Proof

no: liveness and resource use.
