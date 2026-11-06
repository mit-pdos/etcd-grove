---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/bbolt#1311 issue open: a failed Commit after its meta reached the file (our report); a different consequence of a torn meta write
blocks-proof: no
---

# bbolt: a database restored from `Tx.WriteTo` loses both meta pages after two failed commits

A database file written by `Tx.WriteTo` (`etcdctl snapshot save`, and etcd's snapshot sent to a
follower) whose transaction id is odd has its current meta page where the next commit writes its
meta. Each commit's meta write goes to page `txid % 2`, so the database always keeps the other
meta valid. A `WriteTo` copy instead puts the current meta at page 0 whatever its txid. If the
first two commits after opening such a copy both fail while writing their meta page (an I/O
error part-way through the write, or a crash in the middle of it), both metas are left invalid:
- the second failed commit panics (`bolt.DB.meta(): invalid meta pages`) in its rollback, and so
  does a concurrent `Begin`;
- after a crash, the file no longer opens.

A database bbolt committed itself survives the same two faults.

**Expected:** a torn meta write should never destroy the last valid meta, as bbolt's two-meta
design guarantees for its own files: commits alternate between the two meta pages
([`internal/common/meta.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/meta.go#L53-L54)).

**Impact:**
- **Who.** Users who restore or install a database from `WriteTo`/`Copy`/`CopyFile`: etcd's
  snapshot restore (`etcdutl snapshot restore`), and a follower installing a leader's snapshot.
- **When.** Half of all copies are affected (odd txids), and only until the first successful
  commit after opening.
- **How.** It needs two meta-write failures (I/O errors, or crashes during the write) in a row
  before that commit: a double fault.
- Present in v1.5.0 and on `main`.

**Reproduction:** `TestWriteTo_OddTxid_TornMetaWrites` in
[`issues/bbolt-writeto-meta-parity/writeto_meta_parity_test.go`](bbolt-writeto-meta-parity/writeto_meta_parity_test.go)
(package `bbolt`: it injects a meta write that writes 72 of the page's bytes and then fails,
through `db.ops.writeAt`, as the test of bbolt#1311 does), copied into the root of
etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16), go1.27.3 linux/amd64:

```
$ go test . -run TestWriteTo_OddTxid_TornMetaWrites -count=1 -v
=== RUN   TestWriteTo_OddTxid_TornMetaWrites/restored=false
=== RUN   TestWriteTo_OddTxid_TornMetaWrites/restored=true
    writeto_meta_parity_test.go:91: commit 2 after a torn meta write panicked: bolt.DB.meta(): invalid meta pages
--- FAIL: TestWriteTo_OddTxid_TornMetaWrites (0.00s)
    --- PASS: TestWriteTo_OddTxid_TornMetaWrites/restored=false (0.00s)
    --- FAIL: TestWriteTo_OddTxid_TornMetaWrites/restored=true (0.00s)
```

**Cause:** `Tx.WriteTo` writes the transaction's meta (txid `T`) to page 0 and a copy with `T-1`
to page 1
([`tx.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/tx.go#L438-L462)).
For an odd `T` the sequence is:
1. The next commit has txid `T+1` and writes page `(T+1) % 2 = 0`, the current meta.
2. If that write is torn, `db.meta()` falls back to page 1 (`T-1`).
3. The next commit then has txid `T` and writes page `T % 2 = 1`, the only valid meta.

The fix: write txid `T` at page `T % 2` and `T-1` at the other. This is commit `e1fae5c` of
`upamanyus/bbolt`'s branch `goose-lean-v2`, which also adds the test. With it the test passes, and
v1.5.0's test suite passes.

## Proof

no: fixed on the goosed fork (`e1fae5c`, `goose-lean-v2`; D21 of bbolt's API spec,
`notes/bbolt-spec-decisions.md`), which bbolt's own spec needs: `fileHolds` (what `Open` assumes
of a file) requires the current meta at page `txid % 2`, since without it a torn meta write can
panic, and etcd's snapshot path asserts `fileHolds` of `WriteTo`'s images
(`Snapshotter.SaveDBFrom`, `DBFilePath`), which is false for odd txids without the fix. The
top-level results rest on bbolt's `_kv` trust boundary, not on bbolt's proof (`issues/README.md`:
bbolt's own proofs are outside them).
