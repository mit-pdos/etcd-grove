Title: Data race between `MemoryStorage.InitialState` and `MemoryStorage.SetHardState`

### What happened?

With the race detector on (`go test -race`): one goroutine calls `SetHardState` on a `MemoryStorage` while another goroutine calls `InitialState` on the same `MemoryStorage`. The race detector reports a data race between the two calls (output trimmed):

```
WARNING: DATA RACE
Write at 0x00c000330008 by goroutine 10:
  go.etcd.io/raft/v3.(*MemoryStorage).SetHardState()
      .../storage.go:140 +0x92
  go.etcd.io/raft/v3.TestStorageInitialStateConcurrent.func1()
      .../storage_test.go:287 +0x171

Previous read at 0x00c000330008 by goroutine 9:
  go.etcd.io/raft/v3.(*MemoryStorage).InitialState()
      .../storage.go:133 +0x476
  go.etcd.io/raft/v3.TestStorageInitialStateConcurrent()
      .../storage_test.go:289 +0x30d
--- FAIL: TestStorageInitialStateConcurrent (0.00s)
    testing.go:1712: race detected during execution of test
```

This affects any application that calls `InitialState`, directly or by creating a node on the storage, while another goroutine writes to the same `MemoryStorage` (`SetHardState`, `ApplySnapshot` or `CreateSnapshot`).

### What did you expect to happen?

`InitialState` should be safe to call concurrently with the other methods of `MemoryStorage`, whose documentation says that its mutex protects access to all of its fields.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestStorageInitialStateConcurrent`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-memorystorage-initialstate-unlocked/storage_test.go#L279-L292) on branch [`upamanyus/etcd-raft:fix/raft-memorystorage-initialstate-unlocked`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-memorystorage-initialstate-unlocked), off `main` (1931ff5be). On `main`, `go test -race -run TestStorageInitialStateConcurrent .` fails as above, in every run.

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (1931ff5be), go1.26.9 linux/amd64.

</details>
