Title: Member with auth enabled panics on a permission check while it restores a snapshot from the leader

### What happened?

With auth enabled, a member that has fallen behind the leader crashes in the permission check of a read:

1. A follower is cut off from the other members while the leader commits enough writes to compact its log past the follower.
2. Goroutines keep calling the follower's `AuthStore().IsRangePermitted` for `root`, the check of every serializable `Range`.
3. Once the follower reconnects, the leader sends it a snapshot. While the follower restores the snapshot, one of the checks panics (output trimmed):

```
panic: runtime error: invalid memory address or nil pointer dereference [recovered, repanicked]
[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0xc86ff3]
go.etcd.io/bbolt.(*Tx).Bucket(...)
	/home/ubuntu/go/pkg/mod/go.etcd.io/bbolt@v1.5.0/tx.go:112
go.etcd.io/etcd/server/v3/storage/backend.(*baseReadTx).UnsafeRange(0x28c2a190a0f0, {0x1dda048, 0x1e6e528}, {0x28c2a23c4ac0, 0x4, 0x8}, {0x0, 0x0, 0x0}, 0x0)
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/storage/backend/read_tx.go:103 +0x233
go.etcd.io/etcd/server/v3/storage/schema.unsafeGetUser(0x28c2a1925200, {0x72d5541ff200, 0x28c2a190a0f0}, {0x10057f0, 0x4})
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/storage/schema/auth_users.go:57 +0x9d
go.etcd.io/etcd/server/v3/storage/schema.(*authReadTx).UnsafeGetUser(0x28c2a153afa8?, {0x10057f0?, 0x4?})
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/storage/schema/auth_users.go:53 +0x4d
go.etcd.io/etcd/server/v3/auth.(*authStore).isOpPermitted(0x28c2a156ba00, {0x10057f0, 0x4}, 0x4, {0x28c2a3d82a9c, 0x3, 0x3}, {0x0, 0x0, 0x0}, ...)
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/auth/store.go:883 +0x4af
go.etcd.io/etcd/server/v3/auth.(*authStore).IsRangePermitted(0x3?, 0x1b99c00?, {0x28c2a3d82a9c?, 0x3?, 0x3?}, {0x0?, 0x0?, 0x0?})
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/server/auth/store.go:906 +0x4e
go.etcd.io/etcd/tests/v3/integration.TestV3AuthRangePermittedDuringSnapshotRestore.func1()
	/home/ubuntu/etcd-fixes/etcd-auth-snapshot-closed-backend-panic/tests/integration/v3_auth_test.go:705 +0xd9
```

Serializable `Get`s from a client authenticated as `root` instead crash the follower the same way, from `kvServer.Range`, in 19 of 20 runs. This can happen to any member with auth enabled that restores a snapshot while clients send it serializable reads.

### What did you expect to happen?

The follower should answer every permission check and serializable `Get` during the snapshot restore, and keep running.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestV3AuthRangePermittedDuringSnapshotRestore`](https://github.com/upamanyus/etcd/blob/fix/etcd-auth-snapshot-closed-backend-panic/tests/integration/v3_auth_test.go#L673-L718) on branch [`upamanyus/etcd:fix/etcd-auth-snapshot-closed-backend-panic`](https://github.com/upamanyus/etcd/tree/fix/etcd-auth-snapshot-closed-backend-panic), off `main` (bf9cadf04). From `tests/`, `go test ./integration -run TestV3AuthRangePermittedDuringSnapshotRestore -count=1` panics as above on `main` in 20 of 20 runs, with or without `-race` (with `TMPDIR` on tmpfs, 12 of 20 without `-race`).

### Anything else we need to know?

Watch creation, lease keep-alives, `Authenticate` and maintenance requests check permissions the same way and may crash the member too (not tested).

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (bf9cadf04), go1.27.3 linux/amd64; the integration test only, no binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The test's cluster: 3 members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`, auth enabled with a `root` user.

</details>
