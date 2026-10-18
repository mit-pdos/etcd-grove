Title: storage/backend: invalidate the ConcurrentReadTx cache on commit

`ConcurrentReadTx` reuses its cached copy of the read buffer while the buffer's version is unchanged ([backend.go](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/storage/backend/backend.go#L321-L347)), and only a write-back increments the version ([tx_buffer.go](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/storage/backend/tx_buffer.go#L113-L115)). A commit empties the read buffer, whose writes are now in the new bolt read transaction, in [`readTx.reset`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/storage/backend/read_tx.go#L133-L138), but leaves the version unchanged, so the next `ConcurrentReadTx` reads the buffer from before the commit over the new bolt transaction. This PR increments the version in `readTx.reset`.

Fixes #<issue>

`TestConcurrentReadTxAfterCommit` runs the issue's example; it fails on `main` and passes with this change.

Written with the assistance of generative AI; I reviewed and tested every change.
