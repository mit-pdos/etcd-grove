---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22395 pr open: same root cause and fix (checkIntervals reads a from-key delete as empty); does not mention the panic, says not a security fix
  - etcd-io/etcd#22445 issue closed: same root cause, closed as a duplicate of #22395
  - etcd-io/etcd#22446 pr closed: same fix, closed as a duplicate of #22395
blocks-proof: yes
---

# etcdserver: a txn that deletes from a key on and then puts it with IgnoreValue panics every member, permanently

A transaction that deletes every key from `k` on (`clientv3.OpDelete(k, clientv3.WithFromKey())`)
and then puts `k` with `IgnoreValue` or `IgnoreLease` passes the gRPC layer's checks, is committed,
and then panics the apply loop of every member with `index out of range [0] with length 0`. The
entry is in every member's WAL and the consistent index is not persisted past it, so a restarted
member applies it again and panics again: the cluster stays down. Any client allowed to write `k`
can do this with one request.

**Reproduction:** `TestTxnDeleteFromKeyThenIgnorePut` in
[`issues/etcd-txn-delete-then-ignore-put/txn_delete_from_key_then_ignore_put_test.go`](etcd-txn-delete-then-ignore-put/txn_delete_from_key_then_ignore_put_test.go),
copied (as `zz_txn_delete_from_key_then_ignore_put_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ (cd tests && go test ./integration/clientv3 -run '^TestTxnDeleteFromKeyThenIgnorePut$' -count=1)
panic: runtime error: index out of range [0] with length 0 [recovered]
go.etcd.io/etcd/server/v3/etcdserver/txn.put(...)
	.../server/etcdserver/txn/put.go:55 +0x430
go.etcd.io/etcd/server/v3/etcdserver/txn.executeTxn(...)
go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).applyEntryNormal(...)
FAIL	go.etcd.io/etcd/tests/v3/integration/clientv3	0.245s
```

## Proof

yes: what `checkIntervals` gives the transaction's run takes the premise that no delete is a
from-key delete (`ReqOp.noFromKeyDelL`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/CheckNodup.lean`), and the run itself the
premise `IgnOk` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/TxnRun.lean`).

## Notes

The fork's branch `txn-delete-then-ignore-put` (d9ba0e03c) has the same `checkIntervals` change as
#22395, with the test above. Went through etcd's private security process (2026-10-21, `issues/README.md`, "Reporting
privately"); keep this file to what is already public.
