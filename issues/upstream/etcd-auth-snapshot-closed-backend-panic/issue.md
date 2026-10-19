Title: Member with auth enabled panics on a serializable read while it restores a snapshot from the leader

### What happened?

With auth enabled, a member that has fallen behind the leader crashes on an ordinary client read:

1. A follower is cut off from the other members while the leader commits enough writes to compact its log past the follower.
2. A client authenticated as `root` keeps sending serializable `Get`s to the follower, from 32 goroutines.
3. Once the follower reconnects, the leader sends it a snapshot. While the follower restores the snapshot, one of the `Get`s panics the follower's process (output trimmed):

```
panic: runtime error: invalid memory address or nil pointer dereference
[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0xc86d13]

goroutine 2260 [running]:
go.etcd.io/bbolt.(*Tx).Bucket(...)
	/home/ubuntu/go/pkg/mod/go.etcd.io/bbolt@v1.5.0/tx.go:112
go.etcd.io/etcd/server/v3/storage/backend.(*baseReadTx).UnsafeRange(0x292ac61c8190, {0x1dd9b70, 0x1e6e528}, {0x292ac8d80860, 0x4, 0x8}, {0x0, 0x0, 0x0}, 0x0)
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/storage/backend/read_tx.go:103 +0x233
go.etcd.io/etcd/server/v3/auth.(*authStore).isOpPermitted(0x292ac653c200, {0x292ac74ce5cc, 0x4}, 0x4, {0x292ac71a2bf0, 0x3, 0x8}, {0x0, 0x0, 0x0}, ...)
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/auth/store.go:883 +0x4af
go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).Range(0x292ac613dc08, {0x1dd9940, 0x292ac6e95680}, 0x292ac874fae0)
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/etcdserver/v3_server.go:151 +0xcc5
FAIL	go.etcd.io/etcd/tests/v3/integration	1.076s
```

This can happen to any member with auth enabled that restores a snapshot from the leader while a client sends it serializable reads.

### What did you expect to happen?

The follower should answer every serializable `Get` sent during the snapshot restore, or return an error, and keep running.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestV3AuthSerializableGetDuringSnapshotRestore`](https://github.com/upamanyus/etcd/blob/fix/etcd-auth-snapshot-closed-backend-panic/tests/integration/v3_auth_test.go#L672-L717) on branch [`upamanyus/etcd:fix/etcd-auth-snapshot-closed-backend-panic`](https://github.com/upamanyus/etcd/tree/fix/etcd-auth-snapshot-closed-backend-panic), off `main` (6782f5229). From `tests/`, `go test ./integration -run TestV3AuthSerializableGetDuringSnapshotRestore -count=1` panics as above: on `main`, in 10 of 10 runs with the temporary directories on ext4, 5 of 10 on tmpfs.

### Anything else we need to know?

I reproduced the crash with serializable `Get`s only; watch creation, lease keep-alives, `Authenticate` and maintenance requests to the restoring member check permissions the same way and may crash it too (not tested).

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (6782f5229), go1.27.2 linux/amd64; the reproduction is an integration test, with the members in the test process.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The test's cluster: 3 members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`, auth enabled with a `root` user.

</details>
