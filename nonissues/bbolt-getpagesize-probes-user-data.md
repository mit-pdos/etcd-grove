---
upstream: none
checked: 2026-11-03
links: []
blocks-proof: no
---

# bbolt: with both meta pages unreadable or damaged, `Open` can take the page size from a user value

When `Open` cannot get the page size from the first meta page, it probes the file at `1024 << i`
(1 KiB to 16 MiB). It takes the page size from the first probe that holds a checksum-valid meta
(magic, version, FNV-64a checksum). A probe is also skipped when its read fails, so the probing
goes on past a read error as if the page held garbage.

So when **both** meta pages are unusable, the probes reach page 2 (8 KiB) and beyond, where user
data lives. Both reads may fail, both metas may be damaged, or one of each. A value written by
`Put` whose bytes hold a checksum-valid meta at such an offset (in an overflow page, where bbolt
stores a large value verbatim) then sets the database's page size. `Open` continues with a
page size and a meta the database never had, instead of failing.

**Why not an issue:** a hardening finding that needs a double fault, found by code reading:
- **Two faults.** A single fault is caught by the second meta page: if one meta read fails or
  one meta is torn, the other is valid and the probe stops at offset 4096. bbolt writes one meta
  per commit, alternating between the pages, so a normal crash damages at most one.
- **No longer reachable through read errors on the fork.** The goose fork returns a meta read
  error instead of probing past it. There, only two checksum-invalid metas reach user pages: a
  double corruption, in which `Open` cannot be correct anyway, but should fail rather than pick a
  user value's fake meta.
- **Not etcd's case.** etcd's values are client data, so a forged meta inside a value is
  possible. But the double fault is a media failure or a corrupted file.

## Proof

no. bbolt's API spec (2026-11-03, D18, decided by the user) is of the goose fork with
this change, against v1.5.0:
- `getPageSizeFromFirstMeta`, and each probe of `getPageSizeFromSecondMeta`, return a `ReadAt`
  error other than `io.EOF`;
- `getPageSize` returns any error other than `ErrInvalid`.

Probing past page 1 then needs both metas read and checksum-invalid. `fileHolds` (the file `Open`
assumes) requires one valid meta, so the probe stops at page 0 or 1, and no clause about user
values is needed. Without the change, `fileHolds` would have to assume that no user value holds a
valid meta at a probed offset, which no `Commit` can re-establish (`Put` takes arbitrary bytes).
Found in a review of bbolt's API spec (2026-11-03, `notes/bbolt-spec-decisions.md`), after the old
bbolt proof's note
(`old/bbolt/notes/STATUS-bbolt.md`, "a value holding a forged one").

## Notes

- **The code.** `db.go`: `getPageSize`, `getPageSizeFromFirstMeta`, `getPageSizeFromSecondMeta`.
  Identical in v1.5.0, on the fork `goose-lean` (3207bac) before the change, and on
  etcd-io/bbolt@a4ef197.
- **The change.** The fork's commit `7c837ad` (`upamanyus/bbolt`, `goose-lean-v2`;
  `notes/bbolt-spec-decisions.md`, D18, has the diff against v1.5.0). It builds, and v1.5.0's `TestOpen*` and `TestDB_Open*` tests pass with it (go1.27.3, 2026-11-03).
- **Hardening upstream.** The same change could be proposed upstream. A further check would
  accept a probed meta only if its page size equals the offset it was found at, since meta 1 sits
  at offset `pageSize`. A fake meta can still claim that, so the read-error change is the
  substantive part; with both metas damaged, failing is the only correct outcome.
