---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# bbolt: a read transaction of txid 0 lets `ReleasePendingPages` free pages it reads

`freelist.ReleasePendingPages` releases the pending pages between read transactions with
`releaseRange(minid, tid-1)` for each open reader's `tid`, in `common.Txid` (`uint64`) arithmetic.
For a reader of txid 0, `tid-1` wraps to `math.MaxUint64`: `releaseRange(0, MaxUint64)` covers every
pending page, whose allocating transaction (unknown, 0, or any other) then lies in the range. It
takes **two calls** with the reader still open: on the first, the fresh pending entry has
`lastReleaseBegin = 0`, so `releaseRange(0, ...)` skips it (`shared.go:183`), but the call's last
`releaseRange(1, MaxUint64)` sets `lastReleaseBegin = 1`; on the second, `releaseRange(0, MaxUint64)`
no longer skips it and releases the page, including the pages of txid 0's tree that a later writer
freed. A writer may then reallocate and overwrite them while the reader still reads them (checked
by a test in a copy of the module, review 4d-1: reader 0, `Free(1, page 3)` with allocator 0, two
`ReleasePendingPages`, then `Allocate(2, 1)` returns 3). A reader at txid `MaxUint64` is the
mirror case: `tid+1` wraps to 0 and the final `releaseRange(0, MaxUint64)` releases everything.

A reader has txid 0 only when the database's current meta has txid 0, i.e. when meta page 1 (txid
1, written by `db.init`) is invalid at `Open` while meta page 0 is valid: a file whose `init` write
was torn, or a damaged meta 1. `db.meta()` then picks meta 0; read transactions take its txid.

**Why not an issue:** found by code reading (U3 of the bbolt proof, `notes/bbolt-proof-plan.md`,
finding 6); no test. A fresh database's current meta has txid 1 and txids only grow, so the
reachable case needs a damaged meta page 1 at `Open`.

## Proof

no: `fileHolds` excludes it: a well-formed file's current meta has txid at least 1
(`Inv/FileHolds.lean`'s `fileOK`, the `fileHolds` docstring in `Spec/go_etcd_io/bbolt/Api.lean`;
decided 2026-11-04: bbolt never leaves a current meta of txid 0 after `init`, since an in-process
torn write is excluded (D22), the fork's `init` is crash-safe, and `WriteTo` copies a database of
txid at least 1). `Open` (U11) gets `1 ≤ C.txid` from it for `metaR`, which `store_release` needs
(every reader txid at least 1).

The freelist's `ReleasePendingPages` spec takes `readersOk` (no reader at txid 0 or `2^64-1`;
`Spec/go_etcd_io/bbolt/internal/freelist/Interface__ReleasePendingPages.lean`).

## Notes

Code: `internal/freelist/shared.go`, `ReleasePendingPages` (`t.releaseRange(minid, tid-1)`), at the
fork's pinned bbolt revision.
