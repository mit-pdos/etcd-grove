---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: yes
---
# clientv3/leasing: a write that failed and was resent may take effect after a later write

A `Put` or `Delete` through the leasing KV whose first attempt fails with an error that does not
settle whether it took effect (a timeout, a lost connection) is sent again; if the resend
succeeds, the call returns success, but the first attempt may still be applied later, after
writes the caller made since: `Put(k, "v1")` then `Put(k, "v2")`, both successful, may leave `v1`.

**Why not an issue:** found by code reading, confirmed by a second reader; no test (it needs a
fault after the first attempt reached the member). Cause: [`put`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go) and
[`delete`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go) call `revoke`, which resends the operation, whenever `tryModifyOp`
returned an error.

## Proof

yes: the leasing contract takes the caller's update for a write persistent, fired any number of
times, also after the return (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`, header, 1.).
