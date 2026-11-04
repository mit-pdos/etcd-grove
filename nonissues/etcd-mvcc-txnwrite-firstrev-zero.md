---
upstream: none
checked: 2026-11-04
links:
blocks-proof: no
---

# mvcc: a write transaction's FirstRev is always 0, not the compaction revision

`TxnWrite.FirstRev()` returns 0 on every write transaction, also after a compaction, where
[`ReadView.FirstRev`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kv.go#L41-L44)
documents "the first KV revision at the time of opening the txn. After a compaction, the first
revision increases to the compaction revision." [`store.Write`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/kvstore_txn.go#L174-L184)
builds `storeTxnCommon{s, tx, 0, 0, trace}` and never sets `firstRev`; `store.Read` sets it to
`compactMainRev`.

**Why not an issue:** documentation only: no etcd caller reads `FirstRev` from a write transaction.
The only non-test caller, [`checkRange`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/txn/range.go#L174-L184)
(`req.Revision < rv.FirstRev()` gives `ErrCompacted`), is reached through `checkTxn` with the read
transaction `txn.Txn` opens before it opens the write one
([`txn.go`](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/txn/txn.go#L43-L54)),
and a read-only `TxnWrite` (`NewReadOnlyTxnWrite`) forwards to its read transaction. A caller that
checked a range of a write transaction the same way would never get `ErrCompacted`.

## Proof

no: `storeTxnCommon.FirstRev`'s spec returns the field as it is
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/storeTxnCommon__FirstRev.lean`), and the proofs of the
write transaction carry `firstRev = 0` (`InvStore.lean`, `storeTxnWrite__Range.lean`); the
compaction-revision bound is stated only for read views (`readView__FirstRev.lean`). The mvcc model
test (`examples/etcd/mvccmodel`) accepts either value for a write transaction.

## Notes

`TestTxnWriteFirstRev` in
[`etcd-mvcc-txnwrite-firstrev-zero/txnwrite_firstrev_test.go`](etcd-mvcc-txnwrite-firstrev-zero/txnwrite_firstrev_test.go),
copied (as `zz_firstrev_test.go`) into `server/storage/mvcc` at
etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-02), go1.27.3 linux/amd64: five puts,
`Compact(4)`, then the two transactions:

```
$ (cd server && go test ./storage/mvcc -run '^TestTxnWriteFirstRev$' -count=1)
--- FAIL: TestTxnWriteFirstRev (0.01s)
    zz_firstrev_test.go:44: Write().FirstRev() = 0, Read().FirstRev() = 4: want both the compaction revision 4
```

A fix would set `firstRev` from `s.compactMainRev` in `store.Write` (under `revMu`), or say on
`ReadView.FirstRev` that a write transaction returns 0.
