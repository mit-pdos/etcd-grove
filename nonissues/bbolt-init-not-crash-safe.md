---
upstream: known
checked: 2026-11-02
links:
  - etcd-io/bbolt#567 issue closed: this bug (power failure during initialization), closed 2026-02-21 by documenting it
  - etcd-io/bbolt#1151 pr merged: the documentation (README, known issues: "Bolt db can be corrupted during the initialization phase due to abrupt power failure")
  - etcd-io/etcd#16596 issue closed: etcd fails to start after a power failure during the first start (found with LazyFS)
blocks-proof: yes
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

yes, since 2026-11-24 (etcd_safe: a member crashing inside its first backend open): see "The window between init's two syncs" below. Before:

no: the top-level adequacy proof needs no fix on the goosed fork for it; a crash-safety theorem of bbolt's `Open` would be false here; bbolt has no crash proof (the
old one had no crash semantics, `old/bbolt/notes/STATUS-bbolt.md`), and the example minibolt
initializes differently on purpose (`examples/osfs/bboltfs/README.md`, "One deliberate difference from
bbolt: init"), as a bbolt proof would need. The goose target fork carries that fix (2026-11-02,
`upamanyus/bbolt` branch `goose-lean`, 3207bac): `init` writes the four pages with zero meta
pages and syncs, then the metas and syncs, and `Open` runs `init` again when every byte the file
holds of its meta pages is zero (tested by `TestOpen_InterruptedInit`). This also matched damaged databases. The fork now
checks the size and contents of the whole first write before reinitializing.
[Regression and fix](../issues/bbolt-open-zero-meta-reinitializes-data.md)

## Notes

The proposals upstream (bbolt#567's discussion): write pages 2-3 and sync before the metas; re-run
`init` when no meta validates; or write a temporary file, sync, and rename it into place.

## The window between init's two syncs (2026-11-24, etcd-dist D6 C-I1)

The fork's fix covers a crash before `init`'s first `fdatasync` (`needsInit` accepts zero metas over
any subset of the first write's bytes). It does not cover a crash between the first and the second
`fdatasync`, while the two meta pages (written in one `writeAt` of two pages) are unsynced: the file
extension's crash model keeps each unsynced byte old or new independently (`CrashFile`,
`GooseLang/Ext/Fs/Impl.lean`), so both meta pages can be torn (part zero, part new). Then `metasZero` is
false (`needsInit` does not reinitialize), `getPageSize` falls back to the default page size (page 0
readable), and `mmap` finds both metas invalid (`db.go:601-605`, at `ca88bb6a`): `Open` returns an error,
and etcd's `newBackend` calls `bcfg.Logger.Panic("failed to open database")`
(`server/storage/backend/backend.go:235`). Found by reading, no test. On real disks a meta's checksummed
fields (its first 64 bytes) lie in one 512-byte sector, which a power loss does not tear, so each meta is
zero or whole and `Open` succeeds (meta 1 or meta 0 valid, or both zero and `needsInit` true): the gap is
between the model's per-byte crash and sector atomicity, not a bug seen on hardware.

**Blocks the proof** of `etcd_safe` (a member machine may crash inside its first start's `bolt.Open`):
C-I1 (`Proof/.../storage/backend/CrashInterim.lean`) is restricted to databases past `Open`, and C-I3
(`Proof/.../etcdserver/CrashInterim.lean`) excludes such a file. Ways out: a fork change, `needsInit`
also reinitializing a file of exactly four pages whose pages 2 and 3 are the first write's image (or
zero) and whose metas are each zero or invalid (only `init` writes such a file: a database past `init`
has a valid meta, and its first commit grows the file past four pages); or a sector-atomicity premise in
the file extension's crash model (a trusted change).
