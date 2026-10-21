---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/bbolt#262 issue closed: a fault in rollback's db.meta (a concurrent remap), a different cause
  - etcd-io/bbolt#152 issue closed: a rollback panic with NoFreelistSync, a different path
  - etcd-io/bbolt#331 issue closed: a crash between the data pages' sync and the meta's, a different path
candidate: issues/upstream/bbolt-commit-meta-error-frees-reader-pages/
---

# A `Commit` whose meta write fails after reaching the file frees pages open readers still use

- **Status**: a bug (bbolt's MVCC guarantee: a read transaction's snapshot can be overwritten by a
  later writer), reachable on an I/O error, reproduced by a Go test. A second, milder
  consequence: `Commit` returns an error although its writes took effect. Not reachable through
  etcd, whose backend exits on any `Commit` error (`server/storage/backend/batch_tx.go`,
  `batchTx.commit`: `lg.Fatal("failed to commit tx")`); any bbolt user that keeps the `DB` open
  after a failed `Commit` meets it.
- **Where**: bbolt v1.5.0 (the version the bbolt proof pins, branch `bbolt`); upstream `main`
  unchanged as of 2026-10-21 (a4ef197).
  - `tx.go:267-271`, `Tx.Commit`: on a `writeMeta` error it calls `tx.rollback()`.
  - `tx.go:595-625`, `Tx.writeMeta`: writes the meta page through `db.ops.writeAt`, then
    `fdatasync`; either can fail after the meta's bytes are in the file.
  - `tx.go:323-343`, `Tx.rollback`: `freelist.Rollback(txid)`, then
    `freelist.Reload(db.page(db.meta().Freelist()))`.
  - `db.go:1141-1162`, `DB.meta`: the meta with the higher txid if it validates.
- **What happens**:
  1. A reader is open on the current tree.
  2. A writer changes keys; its spill frees the pages of the old leaves (pending for its txid:
     the open reader may still read them). `commitFreelist` writes the new freelist page:
     every free and pending id, these included.
  3. `writeMeta` writes the new meta. The write reaches the file (the mapping shows it), then
     reports an error: `fdatasync` fails (EIO), or a short write is followed by an error after
     the meta's first 80 bytes.
  4. `Commit` calls `rollback()`. `Rollback(txid)` drops the writer's pending entry. `db.meta()`
     now returns the *new* meta (valid checksum, higher txid), so `Reload` reads the *new*
     freelist page, and `NoSyncReload` removes only the ids still pending: the pages the writer
     freed become free.
  5. The next writers allocate those pages and overwrite them while the reader of step 1 still
     reads them.

  Also, the new meta stays current: new readers see the "failed" transaction's writes, and so
  does the next writer.

  Reproduction: [`bbolt-commit-meta-error-frees-reader-pages/repro_test.go`](bbolt-commit-meta-error-frees-reader-pages/repro_test.go)
  (copy into bbolt's package directory; `go test -run TestReproMetaWriteFail`). It replaces
  `db.ops.writeAt` with one that writes, then returns an error for the meta pages. Output at
  v1.5.0:

  ```
  repro_test.go:81: commit returned: injected error after the meta page was written
  repro_test.go:83: a new reader after it sees k0100 = "nnnnnnnnnn"...
  repro_test.go:107: the open reader's snapshot changed under it: Get now "eeeeeeeeee"..., the value read before now "eeeeeeeeee"...
  --- FAIL: TestReproMetaWriteFailFreesReaderPages
  --- PASS: TestReproMetaWriteFailControl
  ```

  The control (no injected error) keeps the reader's snapshot (`oooo…`). Here the reader's
  pages hold another writer's values; a page reused as a branch page instead would give the
  reader a corrupt tree (out-of-bounds reads).
- **Expected**: a read transaction's snapshot does not change while it is open, whatever
  `Commit` returns (bbolt's MVCC: a page is reused only once no open transaction can see it); and
  a `Commit` that returns an error has not taken effect, or says that its outcome is unknown.
- **How the proof handles it**: the bbolt proof (branch `bbolt`, unfinished) found it stating
  `Commit`'s error paths: `Tx.rollback`'s writer spec (`Spec/go_etcd_io/bbolt/Tx__rollback_w.lean`)
  requires the current meta to be the old one; `Commit`'s spec (not written yet) must give back
  nothing when `writeMeta` fails with a reader open. Design note: `notes/bbolt-proof-plan.md`,
  "The spill and `Commit`".
- **Possible fixes**: in `Tx.rollback`, when `db.meta()` is the transaction's own meta (its write
  reached the file), leave the freelist as a successful `Commit` does (keep `pending[txid]` and the
  allocations) and only close the transaction; this also covers `Update`'s rollback after a panic in
  the same window. The candidate (`issues/upstream/bbolt-commit-meta-error-frees-reader-pages/`) does
  this; its `meta.md` explains why the others are worse: reloading from the freelist of the meta the
  transaction started from is wrong (the new meta stays current, and the old freelist lists the new
  tree's pages as free); a fix in `Commit` misses the panic path; undoing the meta write is not
  reliable; treating the error as fatal for the `DB` is a new API decision that still needs this fix
  for open readers.
- **Found**: 2026-10-12, the bbolt proof (`Commit`'s error paths); reproduced 2026-10-19.
