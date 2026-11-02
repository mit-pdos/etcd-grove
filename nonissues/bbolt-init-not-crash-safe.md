---
upstream: known
checked: 2026-11-02
links:
  - etcd-io/bbolt#567 issue closed: this bug (power failure during initialization), closed 2026-02-21 by documenting it
  - etcd-io/bbolt#1151 pr merged: the documentation (README, known issues: "Bolt db can be corrupted during the initialization phase due to abrupt power failure")
  - etcd-io/etcd#16596 issue closed: etcd fails to start after a power failure during the first start (found with LazyFS)
blocks-proof: no
---

# bbolt: a crash while creating a new database can leave a file that never opens

`init` writes a new database's four pages (two metas, the freelist, the root leaf) in one write
and one `fdatasync`, with no ordering between them. A crash before the `fdatasync` completes can
keep a valid meta and lose the freelist or root page (or keep less than a page): the next `Open`
sees a non-empty file, does not re-run `init`, and fails or panics (`invalid freelist page`, a
SIGBUS past the end of the file, `file size too small`), at every `Open`, until the file is
deleted.

**Why not an issue:** known upstream and documented as a known issue (bbolt#567, #1151, from
etcd#16596, reproduced there with LazyFS); it only affects a database's first creation. No test
here (found by reasoning about Linux's write-back order).

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; a crash-safety theorem of bbolt's `Open` would be false here; bbolt has no crash proof (the
old one had no crash semantics, `old/bbolt/notes/STATUS-bbolt.md`), and the example minibolt
initializes differently on purpose (`examples/bboltfs/README.md`, "One deliberate difference from
bbolt: init"), as a bbolt proof would need. The goose target fork carries that fix (2026-11-02,
`upamanyus/bbolt` branch `goose-lean`, 3207bac): `init` writes the four pages with zero meta
pages and syncs, then the metas and syncs, and `Open` runs `init` again when every byte the file
holds of its meta pages is zero (an interrupted `init`; a database never otherwise has zero meta
pages), with a test (`TestOpen_InterruptedInit`).

## Notes

The proposals upstream (bbolt#567's discussion): write pages 2-3 and sync before the metas; re-run
`init` when no meta validates; or write a temporary file, sync, and rename it into place.
