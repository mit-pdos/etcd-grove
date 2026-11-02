---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---

# backend: a put whose stored value exceeds bbolt's MaxValueSize makes the member exit

A put whose encoded `KeyValue` exceeds bbolt's `MaxValueSize` (`2^31 - 2` bytes) reaches
`bucket.Put`, which fails, and `batchTx.unsafePut` calls `lg.Fatal`: every member exits applying the
entry.

**Why not an issue:** no test (code reading; it needs a 2 GiB request), and unreachable unless
`--max-request-bytes` (default 1.5 MiB; etcd warns above 10 MiB) is raised to about 2 GiB, an absurd
configuration.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the backend's `UnsafePut`/`UnsafeSeqPut` specs take the size bounds as premises
(`Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafePut.lean`), passed to mvcc's
puts as `PutOk` (`BackendBridge.lean`); etcd meets them only while `--max-request-bytes` stays below
about 2 GiB, which it does not check.

## Notes

A fix would cap `--max-request-bytes` below `MaxValueSize` minus the `KeyValue` overhead, or document
the bound on `UnsafePut`. The same size bound reaches auth records (`etcd-auth-record-too-large-fatal`).
