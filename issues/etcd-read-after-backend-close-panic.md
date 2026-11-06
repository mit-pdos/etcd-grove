---
upstream: known
checked: 2026-11-03
links:
  - etcd-io/etcd#22189 issue open: the same root cause (`Cleanup` closes the backend with reads in flight, e.g. after the member's removal), reached from `Maintenance/Status`; not the `Range` path
  - etcd-io/etcd#22190 pr open: the fix of #22189, for `StorageVersion` only; does not fix this
  - etcd-io/etcd#7322 issue closed: the same crash (`tx closed`) on a member removed from an embedded cluster (3.1, 2017)
  - etcd-io/etcd#17223 issue closed: the same nil read transaction at shutdown; closed as fixed by gRPC's `GracefulStop` waiting for handlers, which does not cover a member that stops itself
  - etcd-io/etcd#14256 issue closed: the same `Tx.Bucket` stack at shutdown (3.4)
blocks-proof: no
---

# etcdserver: a member removed from the cluster crashes on the serializable reads it is still serving

When a member is removed from the cluster, it stops its server and closes its backend while its
gRPC server keeps accepting requests; a serializable `Range` (or any read that reaches the backend)
in flight or arriving then dereferences the closed backend's nil read transaction, and the panic
kills the process instead of letting it exit cleanly.

**Reproduction:** `TestV3SerializableReadsOnRemovedMember` in
[`issues/etcd-read-after-backend-close-panic/removed_member_reads_test.go`](etcd-read-after-backend-close-panic/removed_member_reads_test.go),
copied (as `zz_removed_member_reads_test.go`) into `tests/integration` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03), go1.27.3 linux/amd64 (a
3-member cluster with 2000 keys; 8 goroutines send serializable prefix `Get`s to member 2 while
member 0 removes it); 5 of 5 runs panic:

```
$ (cd tests && go test ./integration -run '^TestV3SerializableReadsOnRemovedMember$' -count=1)
panic: runtime error: invalid memory address or nil pointer dereference
[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0xc86d93]

goroutine 2831 [running]:
go.etcd.io/bbolt.(*Tx).Bucket(...)
	go.etcd.io/bbolt@v1.5.0/tx.go:112
go.etcd.io/etcd/server/v3/storage/backend.(*baseReadTx).UnsafeRange(...)
	server/storage/backend/read_tx.go:103 +0x233
go.etcd.io/etcd/server/v3/storage/mvcc.(*storeTxnCommon).rangeKeys(...)
	server/storage/mvcc/kvstore_txn.go:126 +0x909
...
go.etcd.io/etcd/server/v3/etcdserver/txn.Range(...)
	server/etcdserver/txn/range.go:55 +0x18c
go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).Range.func3()
	server/etcdserver/v3_server.go:150 +0x96
...
go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*kvServer).Range(...)
	server/etcdserver/api/v3rpc/key.go:53 +0xfb
FAIL	go.etcd.io/etcd/tests/v3/integration	6.173s
```

**Cause:** on its removal the member stops itself
([`stopWithDelay`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/server.go#L1202)),
and `run`'s deferred stop waits for the server's own goroutines, then calls
[`Cleanup`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/server.go#L942-L962),
which closes the store and the backend; gRPC handlers are not among those goroutines, and the gRPC
server stays up until the embedding program or `etcdmain` stops it. A serializable
[`Range`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/v3_server.go#L138-L151)
checks nothing of the server's state before reading the store, and the backend's last commit has set
its shared read transaction to `nil`
([`unsafeCommit`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/backend/batch_tx.go#L381-L406)),
which [`UnsafeRange`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/backend/read_tx.go#L98-L104)
dereferences.

## Proof

no: shutdown is in scope since 2026-11-06 (the user's decision, `notes/decisions.md`, "mvcc's API:
the store's readers as client-held tokens"), and the API rules this crash out. Every mvcc call that
reads the backend takes a reader token (`mvccReaders γ 1`; a transaction keeps it until its `End`)
and gives it back; `KV.Close.contract` gives no part of the backend back, only `mvccClosed γ`; the
backend's open shares the store holds come back only through `mvccClosed_rest.law`, from
`mvccClosed γ` with **every** reader token (`mvccReaders γ mvccReaderN`)
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`). `backend.Close` needs the whole open token,
so a proved client can close the backend only once it holds every token back, that is once no read
of the store is in flight: exactly what etcd's `Cleanup` does not wait for. A proof of etcd's stop
path over this API has to add that wait (the gate in the notes below), so the bug cannot survive
it. Reading during or after mvcc's own `Close` is allowed (it touches no backend), as in etcd.

## Notes

- What #22189 does not say: the common read path (`Range`, serializable) is reached too, so
  #22190's fix of `StorageVersion` alone leaves the crash; a comment there with this test, or a fix
  in front of the store (reads take a gate shared, `Cleanup` exclusively after the server is marked
  stopped, later reads fail with `ErrStopped`), covers every handler.
- `embed.Etcd.Close` stops the gRPC servers before the server, but falls back to `grpc.Server.Stop`
  after a timeout (open watch streams keep `GracefulStop` from finishing) or at once (TLS with HTTP
  on the same port), and grpc-go's `Stop` does not wait for running handlers unless
  `WaitForHandlers` is set, which etcd does not set: by reading, the same crash is reachable there.
- An earlier reproduction (2026-11-03, at upamanyus/etcd `249d76bea`, upstream `main` of 2026-10 with
  fixes) stopped an embedded server with `e.Server.Stop()` while it served serializable `Get`s: 5 of 5
  runs panicked the same way.
