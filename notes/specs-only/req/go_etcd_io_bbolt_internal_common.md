# Requirements on `go.etcd.io/bbolt/internal/common` (batch 4d)

## from 4c

bbolt's public API (`SpecPlan/Spec/go_etcd_io/bbolt/`, namespace `Bbolt`) is proved over 4d's byte-level
vocabulary (`BboltCommon`); its sketches rely on:

1. **The meta page's round trip and its place in the page** (`Tx.writeMeta.spec`, `Open.spec`,
   `Tx.WriteTo.spec`): `Meta.Write` into a page buffer leaves `withMeta` with the checksum set
   (`metaValid_summed`), `metaOf` reads it back (`meta_withMeta`), and the header plus the meta lie
   in the page's **first 512 bytes** (`pageHeaderSize + metaSize ≤ 512`, a pure fact): the crash
   argument (decision 4c-D1, the sector rule) needs the whole meta inside one aligned sector of the
   page bbolt writes as one aligned OS page.
   ```go
   p := tx.db.pageInBuffer(buf, 0); tx.meta.Write(p)                 // tx.go (writeMeta)
   m := *tx.meta; *page.Meta() = m; page.Meta().DecTxid(); page.Meta().SetChecksum(page.Meta().Sum64()) // tx.go (WriteTo)
   ```
2. **A node written to a page reads back** (`writeNode_read`, `pageItems`), with its extent
   (`overflow`) sized by `node.size()`, and an inline bucket's value (`encInBucket` plus a leaf
   page within the value) read by `openBucket`/`InlinePage` (`Bucket.Bucket.spec`,
   `Bucket.spill.spec`, `Bucket.CreateBucket.spec`'s empty inline bucket, `bucket.write()`).
3. **Element reads for cursors** (`leafKeySlice`, `leafValueSlice`, `branchKeySlice`, the
   `BucketLeafFlag` of a leaf element): a slice into the page's bytes, which `Bbolt.txBytes`
   realizes while the transaction keeps the page mapped (`Cursor.*`, `Bucket.Get.spec`).
4. **Chunked page writes** (`Tx.write.spec`): `UnsafeByteSlice(p, written, 0, sz)` of a page's
   bytes for `sz ≤ MaxAllocSize - 1`, the chunks covering the extent in order.
5. **A whole file image's decoding**, to realize `Bbolt.boltImage bs D` and `Bbolt.fileHolds`'
   well-formedness: the meta pages at `0` and `4096` (`metaOf`, `metaValid`, the newest valid by
   txid), the tree's pages by `hdrOf`/`pageItems` from the root's `InBucket`, a freelist page by
   `freelistIdsOf`. bbolt defines the tree-to-`Data` map from these; 4d's decoders need only be
   total on any bytes (they are pure functions of `bs`).
