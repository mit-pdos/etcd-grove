Title: Data race between `MemoryStorage.InitialState` and `MemoryStorage.SetHardState`

On `main` (1931ff5be, go1.26.9 linux/amd64), `MemoryStorage.InitialState` races with `SetHardState`: with the race detector on (`go test -race`), one goroutine calling `SetHardState` while another calls `InitialState` on the same `MemoryStorage` reports a data race. `InitialState` should be safe to call concurrently with the other methods of `MemoryStorage`.

`MemoryStorage` embeds a mutex that, as [its comment says](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L105-L108), protects access to all of its fields, and `SetHardState`, `ApplySnapshot`, `CreateSnapshot` and the other methods take it. [`InitialState`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L128-L134) does not: it reads the hard state and the snapshot's `ConfState`, and may set that `ConfState`'s `AutoLeave`, without the mutex. This affects any application that calls `InitialState`, directly or by creating a node on the storage, while another goroutine writes to the same `MemoryStorage`.

Unit test: [`TestStorageInitialStateConcurrent`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-memorystorage-initialstate-unlocked/storage_test.go#L279-L291) on branch [`upamanyus/etcd-raft:fix/raft-memorystorage-initialstate-unlocked`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-memorystorage-initialstate-unlocked), off `main` (1931ff5be). On `main`, `go test -race -run TestStorageInitialStateConcurrent .` fails in every run (output trimmed):

```
WARNING: DATA RACE
Write at 0x00c00012e1e8 by goroutine 10:
  go.etcd.io/raft/v3.(*MemoryStorage).SetHardState()
      .../storage.go:140 +0x92
  go.etcd.io/raft/v3.TestStorageInitialStateConcurrent.func1()
      .../storage_test.go:285 +0xe4

Previous read at 0x00c00012e1e8 by goroutine 9:
  go.etcd.io/raft/v3.(*MemoryStorage).InitialState()
      .../storage.go:133 +0x433
  go.etcd.io/raft/v3.TestStorageInitialStateConcurrent()
      .../storage_test.go:287 +0x2cb
--- FAIL: TestStorageInitialStateConcurrent (0.00s)
    testing.go:1712: race detected during execution of test
```

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
