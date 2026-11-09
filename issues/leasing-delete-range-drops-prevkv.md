---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: yes
---
# clientv3/leasing: a range delete through the leasing KV ignores `WithPrevKV`

`Delete(ctx, key, WithPrefix(), WithPrevKV())` (or `WithRange`, `WithFromKey`) through the leasing
KV returns no previous key-values: `PrevKvs` is always empty, whatever was deleted. A delete of a
single key, and the same range delete through the client, return them.

**Expected:** the leasing KV should honor the delete's options, as it implements
[`clientv3.KV`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/kv.go),
whose `WithPrevKV` returns the deleted key-value pairs.

**Impact:** any user of `leasing.NewKV` that deletes a range with `WithPrevKV` and reads the
response (for instance to learn which keys it removed) gets nothing. Every release with the leasing
KV.

**Reproduction:** `TestLeasingDeleteRangePrevKV` in
[`issues/leasing-delete-range-drops-prevkv/leasing_delete_range_prevkv_test.go`](leasing-delete-range-drops-prevkv/leasing_delete_range_prevkv_test.go),
copied into `tests/integration/clientv3/lease` at etcd-io/etcd@d622ec57cf46 (2026-11-06), go1.27.3
(also fails at the verified fork's a4d2bb1720b9):

```
$ go test ./integration/clientv3/lease -run '^TestLeasingDeleteRangePrevKV$' -count=1
--- FAIL: TestLeasingDeleteRangePrevKV (0.17s)
        	Error:      	"[]" should have 1 item(s), but has 0
        	Messages:   	expected the deleted key-value with WithPrevKV
FAIL
```

**Cause:** [`deleteRange`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/kv.go#L363-L378)
passes only the key and range end to
[`deleteRangeRPC`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/kv.go#L340-L361),
which builds its own `OpDelete(key, WithRange(end))`, dropping the caller's other options.

## Proof

yes: the leasing contract states the request made without `prevKv`
(`Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`, `execReq`), so the leasing KV does not meet the
client's KV contract for range deletes.

## Fix

Not written: pass the caller's `Op` (or its `prevKV` flag) to `deleteRangeRPC` and build the delete
with `WithPrevKV()` when it is set.
