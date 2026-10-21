Title: raft: take the lock in MemoryStorage.InitialState

`MemoryStorage` embeds a mutex that, as [its comment says](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L105-L108), protects access to all of its fields, and every other method takes it. [`InitialState`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/storage.go#L128-L134) does not: it increments a call counter, reads the hard state and the snapshot's `ConfState`, and may set the `ConfState`'s `AutoLeave`, all without the lock, so it races with `SetHardState`, `ApplySnapshot` and `CreateSnapshot`. This PR takes the lock in `InitialState`.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main` under `go test -race`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
