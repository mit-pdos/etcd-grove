---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: yes
---

# clientv3/leasing: a Put or Delete of a key the leasing KV has not cached is applied twice

Every `Put` or `Delete` through the leasing KV of a key it has not cached, when no other client
holds the key's lease, is committed to etcd twice. A `Put` of a fresh key leaves it at version 2,
and with `WithPrevKV` returns its own key-value as the previous one; a `Delete` of an existing key
returns `Deleted == 0` and no `PrevKvs`, since the second delete finds nothing. Each write also
produces two watch events.

**Expected:** an operation through the leasing KV should be applied once, as through a plain
client, since the leasing KV is a [`clientv3.KV`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/doc.go#L15-L18).

**Impact:** every user of `client/v3/leasing` (or the gRPC proxy with leasing), in the default
configuration: the first write of any key the client has not read. Versions, revisions,
`PrevKv`, `Deleted` counts and watch event streams are wrong; code that checks `Deleted` (did my
delete remove the key?) sees 0.

**Reproduction:** `TestLeasingPutUncachedOnce` and `TestLeasingDeleteUncachedOnce` in
[`issues/leasing-modify-uncached-once/leasing_uncached_once_test.go`](leasing-modify-uncached-once/leasing_uncached_once_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/lease -run '^TestLeasing(Put|Delete)UncachedOnce$' -count=1
--- FAIL: TestLeasingPutUncachedOnce (0.19s)
        	Error:      	Expected nil, but got: &mvccpb.KeyValue{..., Key:[]uint8{0x6b}, CreateRevision:2, ModRevision:2, Version:1, Value:[]uint8{0x61, 0x62, 0x63}, ...}
        	Messages:   	put of a fresh key returned a previous key-value
        	            	expected: 1
        	            	actual  : 2
        	Messages:   	version after one put
        	            	expected: 2
        	            	actual  : 3
        	Messages:   	mod revision after one put
        	            	expected: "abc"
        	            	actual  : "def"
        	Messages:   	previous value of the second put
        	            	expected: 2
        	            	actual  : 4
        	Messages:   	version after two puts
--- FAIL: TestLeasingDeleteUncachedOnce (0.17s)
        	            	expected: 1
        	            	actual  : 0
        	Messages:   	number of keys deleted
        	Error:      	"[]" should have 1 item(s), but has 0
        	Messages:   	previous key-values of the delete
FAIL
```

**Cause:** [`tryModifyOp`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L218-L234)
commits the op and, for an uncached key, returns a successful response with a nil wait channel.
[`put`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L241-L244)
and [`delete`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L388-L391)
take `wc == nil` to mean the commit did not happen and call
[`revoke`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L413-L421),
which commits the same guarded op again.

## Proof

yes: the leasing KV's intended spec (each write applied once) is false; the proof describes the
second commit (`leasing_put`/`leasing_delete`, `Proof/go_etcd_io/etcd/client/v3/leasing/`); the
verified fork carries no fix.

## Fix

**Branch**: `leasing-modify-uncached-once` (upamanyus/etcd, pushed): 7a6077dec test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/leasing: apply a Put or Delete of an uncached key once

`put` and `delete` first call `tryModifyOp`, which commits the op guarded by
`Compare(CreateRevision(pfx+key), "<", rev+1)`, where `(wc, rev) = leases.Lock(key)` is `(nil, 0)`
when the key is not cached. When no client holds the key's lease, the op is applied and
`tryModifyOp` returns `(resp, nil, nil)`. `put` and `delete` then test `err != nil || wc == nil` and
call `revoke`, which commits the same guarded op again; its response is the one returned. So every
Put or Delete of a key the leasing KV has not cached is applied twice.

This PR calls `revoke` only when `tryModifyOp` did not commit the op (`err != nil || resp ==
nil`): it returns a nil response exactly when the transaction failed or did not succeed. The error
path is unchanged. The integration tests put a fresh key and delete a key written by another client
through a leasing KV, and check the version, revisions, previous key-values and `Deleted` count.
