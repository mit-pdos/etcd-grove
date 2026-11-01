---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22209 issue open: same bug (keys_only no longer returns lease since #21791), labeled type/bug, proposed for v3.7.4
  - etcd-io/etcd#22550 pr open: fix for #22209 (records the lease in the key index); ahrtr objects to the design and suggests documenting the limitation
  - etcd-io/etcd#22212 pr closed: earlier fix for #22209 (lessor lookup at the latest revision), closed by its author without review
  - etcd-io/etcd#21791 pr merged: introduced the regression (FastKeysOnly)
blocks-proof: yes
---

# etcdserver: keys-only ranges return lease 0 unless sorted by value (regression in v3.7)

Since v3.7.0 (7624a8a2e, #21791), a keys-only range that is not sorted by value returns every
key-value with `Lease` 0, even for a key attached to a lease; the same range sorted by value returns
the lease, as every keys-only range did before. So `etcdctl get foo --keys-only -w json` reports no
lease for a leased `foo`.

**Reproduction:** `TestKVGetKeysOnlyLease` in
[`issues/etcd-range-keys-only-lease/kv_keys_only_lease_test.go`](etcd-range-keys-only-lease/kv_keys_only_lease_test.go),
copied (as `zz_kv_keys_only_lease_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (sort target 0 is
`KEY`, 1 `VERSION`; the `VALUE` cases pass):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestKVGetKeysOnlyLease$' -count=1)
--- FAIL: TestKVGetKeysOnlyLease (0.18s)
        	Error:      	Not equal:
        	            	expected: 5272766926409042179
        	            	actual  : 0
        	Messages:   	sort target 0
        	(the same for sort target 1, and for both at the leased revision 2)
FAIL
```

## Proof

yes: the server's range model zeroes the lease of a fast keys-only read (`leaseZ`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/InvTxn.lean`), and the client's get model holds only
for gets that are not keys-only (`Proof/go_etcd_io/etcd/cache/v3/InvEtcd.lean`, unit V2).

## Notes

The fork branch `range-keys-only-lease` (01e522548, pushed) stops asking mvcc for the index-only read
(filling the lease from the lessor gives the current lease, wrong at a past revision); #22550's
review prefers documenting the limitation.
