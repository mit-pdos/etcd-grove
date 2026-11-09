---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: yes
---
# clientv3/leasing: a range delete through the leasing KV ignores `WithPrevKV`

`Delete(ctx, key, WithPrefix(), WithPrevKV())` (or `WithRange`, `WithFromKey`) through the leasing
KV returns no previous key-values: `PrevKvs` is always empty, whatever was deleted.

**Why not an issue:** no test run yet (found by code reading, confirmed by a second reader;
deterministic). Recipe: with a leasing KV `lkv` over a one-member integration cluster, `Put(ctx,
"p/a", "1")`, then `d, _ := lkv.Delete(ctx, "p/", WithPrefix(), WithPrevKV())`: `d.Deleted == 1` and
`len(d.PrevKvs) == 0` (a plain client returns one). Cause: `deleteRange` passes only the key and range
end to [`deleteRangeRPC`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go), which builds its own `OpDelete(key,
WithRange(end))`, dropping the caller's options. Move to `issues/` with that test.

## Proof

yes: the leasing contract states the request made without `prevKv`
(`Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`, `execReq`), so the leasing KV does not meet the
client's KV contract for range deletes.
