---
upstream: unchecked
links:
  - etcd-io/bbolt#447 issue closed: "Remove panics in the library code", lists the inode-overflow panic, not this trigger
---

# A NaN `Bucket.FillPercent` makes `Commit` panic (amd64)

- **Status**: an unstated precondition (`FillPercent` must not be NaN) whose violation panics
  `Commit`; reproduced by a Go test at v1.5.0 (amd64). `FillPercent`'s documentation says only
  that it sets the split threshold; bbolt clamps out-of-range values, but not NaN. Not reachable
  through etcd, which sets only `0.9` (`server/storage/backend/batch_tx.go:181`, `backend.go:831`).
- **Where**: bbolt v1.5.0, `node.go`: `splitTwo` (`if fillPercent < minFillPercent ... else if
  fillPercent > maxFillPercent ...`: both false for NaN), `threshold := int(float64(pageSize) *
  fillPercent)`, `splitIndex` (`sz+elsize > uintptr(threshold)`), `write` (`if len(n.inodes) >=
  0xFFFF { panic(...) }`).
- **What happens**: `int(NaN)` is implementation-defined; on amd64 it is `MinInt64`, which
  `splitIndex` compares as the `uintptr` `2^63`, so the threshold is never reached and a leaf of
  `N` entries is split only into `N-3` and `3`. A node of 65538 entries or more then reaches
  `node.write` with at least `0xFFFF` inodes: `panic: inode overflow: 69997 (pgid=4)` from
  `Tx.Commit` → `Bucket.spill` → `node.spill` → `node.write`, with 70000 three-byte keys and empty
  values in one transaction. (On arm64 `int(NaN)` is `0` and the split degenerates to 2-entry
  pages instead.) After the panic the writer lock is held, so a deferred `db.Close()` blocks.

  Reproduction (`examples/axiomcx/bboltnan`, `TestRunPanics`; 0.2 s):

  ```go
  db, _ := bolt.Open(path, 0600, &bolt.Options{})
  tx, _ := db.Begin(true)
  b, _ := tx.CreateBucketIfNotExists([]byte("b"))
  z := 0.0
  b.FillPercent = z / z
  for i := uint64(0); i < 70000; i++ {
  	b.Put([]byte{byte(i >> 16), byte(i >> 8), byte(i)}, []byte{})
  }
  tx.Commit() // panic: inode overflow: 69997 (pgid=4)
  ```
- **Expected**: `FillPercent` is documented as a ratio; a NaN should be treated like any other
  out-of-range value (clamped, or the default used), or documented as forbidden.
- **How the proof handles it**: it did not: `backend.ownWTxG_fill`
  (`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean`) gives the field back with
  any value, and `Tx.Commit_kv` excludes a panic, so the axioms prove that the reproduction
  returns (`notes/axiom-review/bbolt.md`). The backend's only use writes `0.9`
  (`batchTx__unsafePut.lean`).
- **Possible fixes**: in `splitTwo`, `if !(fillPercent >= minFillPercent) { fillPercent =
  minFillPercent }` (true for NaN), or check `math.IsNaN`.
- **Found**: 2026-10-29, by the axiom soundness review of the bbolt axioms (`.claude/skills/axiom`),
  attacking `ownWTxG_fill`.
