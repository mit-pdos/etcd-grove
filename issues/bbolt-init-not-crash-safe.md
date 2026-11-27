---
upstream: known
checked: 2026-11-25
links:
  - etcd-io/bbolt#567 issue closed: this bug (power failure during initialization), closed 2026-02-21 by documenting it
  - etcd-io/bbolt#1151 pr merged: the documentation (README, known issues: "Bolt db can be corrupted during the initialization phase due to abrupt power failure")
  - etcd-io/etcd#16596 issue closed: etcd fails to start after a power failure during the first start (found with LazyFS)
blocks-proof: yes
---

# bbolt: a crash while creating a new database can leave a file that never opens

A power loss while bbolt creates a new database can leave a file that every later `Open` rejects
(`invalid freelist page`, `file size too small`, `invalid database`, `checksum error`), until the
file is deleted. Through etcd: a member that loses power during its first start never starts again
(the backend panics "failed to open database").

**Expected:** `Open` should succeed on any file a power loss during `init` can leave (such a file
holds no committed data), as the known issue's discussion proposes (bbolt#567).

**Impact:** any database's first creation, including every etcd member's first start; known
upstream and documented as a known issue (bbolt#567, #1151, from etcd#16596, reproduced there with
LazyFS); every release through v1.5.0.

**Reproduction:** `TestOpen_InterruptedInit` in
[`bbolt-init-not-crash-safe/init_crash_test.go`](bbolt-init-not-crash-safe/init_crash_test.go),
copied into the root of etcd-io/bbolt@e7a8b2dd498494a3766ba24dd94d3509e5588485 (v1.5.0, the
version etcd's `go.mod` uses), go1.27.3 linux/amd64. Each case writes a crash image of `init`'s
unsynced write (any subset of its bytes) and opens it:

```
$ go test -run TestOpen_InterruptedInit -count=1 .
    init_crash_test.go:115: Open after an interrupted init: invalid database
    init_crash_test.go:115: Open after an interrupted init: file size too small 4096
    init_crash_test.go:115: Open after an interrupted init: checksum error
--- FAIL: TestOpen_InterruptedInit (0.00s)
    --- FAIL: TestOpen_InterruptedInit/metas-torn-every-other-byte (0.00s)
    --- FAIL: TestOpen_InterruptedInit/metas-whole-freelist-lost (0.00s)
panic: invalid freelist page: 0, page type is unknown<00> [recovered, repanicked]
FAIL	go.etcd.io/bbolt	0.009s
```

**Cause:** `init` writes the four pages (two metas, the freelist, the root leaf) in one write
and one `fdatasync`, with no ordering between them. A crash before the `fdatasync` completes can
keep a valid meta and lose the freelist or root page (or keep less than a page): the next `Open`
sees a non-empty file, does not re-run `init`, and fails or panics.

Through etcd: `TestBackendOpensInterruptedInit` (`server/storage/backend/init_crash_test.go` on
`upamanyus/etcd` `goose-lean-crashfixes2`, and `goose-lean-fmt1c-crashfixes` @ `e94f33b50`) panics with v1.5.0 (`failed to open database`,
`invalid database`) on a file whose two meta pages are torn over whole freelist and root pages.

## Proof

yes, since 2026-11-24 (etcd_safe: a member crashing inside its first backend open): see "The window between init's two syncs" below; the fix the proof needs is on the forks since 2026-11-25 (above), and in the verified bbolt since 2026-11-25 (`ea5656d`): `Open`'s proof shows that a well-formed file `needsInit` accepts holds no data (`Proof/go_etcd_io/bbolt/Open/InitPartial.lean`, `openOK_initPartial`), so `Open.spec` is unchanged; the crash proof that uses it is open. Before:

no: the top-level adequacy proof needs no fix on the goosed fork for it; a crash-safety theorem of bbolt's `Open` would be false here; bbolt has no crash proof (the
old one had no crash semantics, `old/bbolt/notes/STATUS-bbolt.md`), and the example minibolt
initializes differently on purpose (`examples/osfs/bboltfs/README.md`, "One deliberate difference from
bbolt: init"), as a bbolt proof would need. The goose target fork carries that fix (2026-11-02,
`upamanyus/bbolt` branch `goose-lean`, 3207bac): `init` writes the four pages with zero meta
pages and syncs, then the metas and syncs, and `Open` runs `init` again when every byte the file
holds of its meta pages is zero (tested by `TestOpen_InterruptedInit`). This also matched damaged databases. The fork now
checks the size and contents of the whole first write before reinitializing.
[Regression and fix](bbolt-open-zero-meta-reinitializes-data.md)

## Fix

**Branch**: `v1.5.0-init-crashsafe` (upamanyus/bbolt, pushed): 19e0771 test and fix
**Base**: etcd-io/bbolt@e7a8b2dd498494a3766ba24dd94d3509e5588485

`init` writes the freelist and root pages with zero metas and syncs, then the metas and syncs;
`Open` (not read-only) initializes again a file of at most four pages whose every byte is zero or
the byte `init` writes there and which is not `init`'s whole image (the empty database's state, so
nothing is lost; a database past `init` holds a byte `init` does not write: a page past the fourth,
or a meta of another txid). This covers both the window before the first sync and the window
between the two syncs, and the files the old single write left. `TestOpen_FileTooSmall` now
commits before truncating (a new database cut to one page is an interrupted init). The etcd fork
uses it through a `replace` (`goose-lean-crashfixes2` @ `d49d01a07`, in `go.mod`, `server`,
`etcdutl`, `tests`). The verified bbolt has the same recovery since 2026-11-25 (`upamanyus/bbolt`
`goose-lean-init-crashsafe` @ `ea5656d`, `etc/goose.py`), written with plain loops for goose (no `bytes.Equal`).

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
C-I1 (`Proof/.../storage/backend/CrashLaws.lean`) is restricted to databases past `Open`, and C-I3
(`Proof/.../etcdserver/CrashInterim.lean`) excludes such a file. Ways out: a fork change, `needsInit`
also reinitializing a file of exactly four pages whose pages 2 and 3 are the first write's image (or
zero) and whose metas are each zero or invalid (only `init` writes such a file: a database past `init`
has a valid meta, and its first commit grows the file past four pages); or a sector-atomicity premise in
the file extension's crash model (a trusted change).

**Fixed on the forks (2026-11-25):** the `v1.5.0-init-crashsafe` fix above re-initializes such a
file (torn metas, whole data pages: `metas-torn-*` in the test), the "fork change" way out. The
verified bbolt's `needsInit` has the same widening since `ea5656d` (2026-11-25).
