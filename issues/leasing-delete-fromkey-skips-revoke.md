---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#22083 issue open: related, not this bug: a `WithFromKey` delete whose range reaches the leasing prefix deletes the leasing KVs' own keys
  - etcd-io/etcd#22118 pr open: related, not this bug: #22083's fix (reject deletes intersecting the prefix); a `WithFromKey` range above the prefix, as here, still skips the revoke
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot; does not list this)
blocks-proof: no
---
# clientv3/leasing: a `WithFromKey` delete does not make other leasing clients drop the keys they cache

After `Delete(ctx, "q", WithFromKey())` through one leasing KV, another leasing KV on the same
prefix that had read and cached a key in the range (`"z"`) keeps returning the deleted value from
its cache, although etcd deleted it; a delete of `"z"` alone, or of a bounded range holding it, makes
the other client drop it first.

**Expected:** a key deleted through one leasing KV should stop being served by every other leasing
KV on the prefix, as the leasing KV's
[package doc](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/doc.go#L15-L45)
says ("serves linearizable reads from a local cache"; a writer makes the owner relinquish the key
first).

**Impact:** clients sharing a leasing prefix, one of which deletes with `WithFromKey` (or
`WithPrefix` of the empty key): the others serve the deleted keys until another write to them, or
until their session ends. Every release with the leasing KV.

**Reproduction:** `TestLeasingDeleteFromKeyRevokes` in
[`issues/leasing-delete-fromkey-skips-revoke/leasing_delete_fromkey_test.go`](leasing-delete-fromkey-skips-revoke/leasing_delete_fromkey_test.go),
copied into `tests/integration/clientv3/lease` at etcd-io/etcd@d622ec57cf46 (2026-11-06), go1.27.3
(also fails at the verified fork's a4d2bb1720b9):

```
$ go test ./integration/clientv3/lease -run '^TestLeasingDeleteFromKeyRevokes$' -count=1
--- FAIL: TestLeasingDeleteFromKeyRevokes (0.23s)
        	Error:      	Should be empty, but was [key:"z" create_revision:2 mod_revision:2 version:1 value:"v"]
        	Messages:   	expected the leasing KV not to return z, deleted on etcd
FAIL
```

**Cause:** an open-ended range has range end `"\x00"`.
[`revokeRange`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/kv.go#L423-L433)
prefixes it like any end and reads the lease keys in `[pfx+key, pfx+"\x00")`, which holds none of the
range's keys (it is empty for every key at or above `"\x00"`), so no lease is revoked; the guard of
[`deleteRangeRPC`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/kv.go#L340-L347)
over the same range holds, and the delete goes through. The cache's own
[`inRange`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/client/v3/leasing/cache.go#L75-L83)
treats `"\x00"` as open-ended; a transaction's `guardRanges` has the same problem.

## Proof

no: the leasing contract claims for another client's cached key only a past state's record
(W0's serializable read), which a stale entry still is.

## Fix

Not written: in `revokeRange` and `deleteRangeRPC` (and `guardRanges`), map the end `"\x00"` to the
end of the lease prefix (`clientv3.GetPrefixRangeEnd(pfx)`), not `pfx+"\x00"`.
