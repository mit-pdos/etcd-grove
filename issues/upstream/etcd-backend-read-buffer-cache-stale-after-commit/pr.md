Title: storage/backend: invalidate the ConcurrentReadTx cache on commit

[`ConcurrentReadTx`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/storage/backend/backend.go#L312-L347) reuses its cached copy of the read buffer while the buffer's version is unchanged, assuming, as its comment says, that only a write-back, which [increments the version](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/storage/backend/tx_buffer.go#L115), makes the copy stale. But at each commit [`readTx.reset`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/server/storage/backend/read_tx.go#L133-L138) empties the buffer, whose writes are now in the new bolt read transaction, without incrementing the version, so the next `ConcurrentReadTx` reads the old buffer over the new bolt transaction. This PR increments the version in `readTx.reset` and adds commits to that comment.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
