# A value above bbolt's `MaxValueSize` makes the backend's put exit the process

- **Status**: open (not filed). An unstated precondition of `BatchTx.UnsafePut` /
  `UnsafeSeqPut`, which mvcc's `put` passes on to its callers without stating it; unreachable
  with the server's default request size limit (1.5 MiB).
- **Where**: at the etcd pin of `etc/goose.py` (`bc8b52a50`): `server/storage/backend/batch_tx.go`
  `batchTx.unsafePut` (`bucket.Put(key, value)`, then `lg.Fatal("failed to write to a bucket")`
  on its error); bbolt v1.5.0 `bucket.go` (`Put` returns `ErrValueTooLarge` for a value above
  `MaxValueSize = (1 << 31) - 2`, `ErrKeyTooLarge` for a key above `MaxKeySize = 32768`);
  `server/storage/mvcc/kvstore_txn.go` `storeTxnWrite.put` (it puts `proto.Marshal` of the
  `mvccpb.KeyValue`, the client's key and value with the revisions, version and lease). The APIs
  (`UnsafeWriter.UnsafePut`, `TxnWrite.Put`) state no size bound.
- **What happens**: a put whose encoded `KeyValue` exceeds `2^31 - 2` bytes reaches
  `bucket.Put`, which fails, and the backend's `Fatal` exits the process. The server bounds a
  request by `--max-request-bytes` (default 1.5 MiB; the configuration only warns above 10 MiB),
  so a member configured with a limit near 2 GiB could exit on a large enough put. Not
  reproduced (it needs a 2 GiB request).
- **Expected**: the bound stated (or checked, with an error) where the request enters, or by
  `UnsafePut`'s documentation.
- **How the proof handles it**: the backend's `UnsafePut`/`UnsafeSeqPut` specs take the bounds
  as premises (`Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeSeqPut.lean`:
  `kb.length ≤ maxKeySize → vb.length ≤ maxValueSize`); mvcc's contract of its backend over the
  real one (`BackendBridge.lean`, `bkPutOk`) passes them to mvcc's puts as the condition
  `PutOk` of `batchTxSpecG`. mvcc's store does not discharge it yet (it uses the instance
  without conditions, `isKeyBackend`): `notes/STATUS.md`, "Unit 4".
- **Possible fixes**: reject a request whose encoded size exceeds bbolt's bound at the server
  (`--max-request-bytes` capped below `MaxValueSize` minus the `KeyValue` overhead); or state
  the bound in `UnsafePut`'s and `TxnWrite.Put`'s documentation.
- **Found**: 2026-10-13, the backend bridge (unit 4, part 2), stating what the backend's
  `UnsafeSeqPut` needs of mvcc's puts.
