---
upstream: none
checked: 2026-11-11
links:
  - etcd-io/etcd#22709 issue open: related, different: ReadAll's ZeroToEnd is not fsynced, so a second crash can bring torn-write residue back (the same decoder rule makes it unrepairable)
  - etcd-io/etcd#6515 issue closed: related: the decoder's torn-write rule (a torn record has an all-zero sector)
  - etcd-io/etcd#11918 issue closed: related, cause unknown: "walpb: crc mismatch" at startup after a crash
blocks-proof: no
---

# wal: a Save cut short inside a sector by a crash makes the WAL unopenable (CRC mismatch, not a torn write)

When the last record of a WAL segment was cut short inside a 512-byte sector (its first bytes on
disk, the rest of that sector zero, as the preallocated segment is), `ReadAll` returns a CRC
mismatch or a protobuf error instead of `io.ErrUnexpectedEOF`: the decoder calls a bad last record
torn only if one of its sectors is all zero. The server's bootstrap repairs only
`io.ErrUnexpectedEOF`, so the member refuses to start ("failed to read WAL, cannot be repaired"),
although the cut record belongs to a Save that had not returned. Linux can leave such an image on
ext4 with default options: the encoder's `PageWriter` flushes from a page-aligned buffer to a
mid-page file offset, and a buffered `write(2)` whose copy stops at a source page boundary (a
source page being migrated by memory compaction) leaves the file page torn there, unlocked, until
the copy resumes; a writeback taking the page in that window, then a power loss before the Save's
`fdatasync` completes, leaves the cut on disk.

**Why not an issue:** the crash image of the test is constructed (the WAL written by `Save` as
etcd does, the file then zeroed from the cut on), not captured: the harness of
`notes/axiom-review/fs-v2-r6/wal/` caught the cut in the page cache once in about 10^7 WAL writes
under forced compaction and never saw it written back torn; the mechanism is measured on disk only
for another program (`fs-v2-r6/e2e`, mechanism A). Without a captured image the bar of
`issues/README.md` (a test reaching the bug as etcd does) is not met.

**Test:** `TestReadAllTornTailMidSector` in [`etcd-wal-torn-tail-mid-sector/tear_test.go`](etcd-wal-torn-tail-mid-sector/tear_test.go),
copied into `server/storage/wal` at etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d
(2026-11-10), go1.27.3:

```
$ go test ./storage/wal -run TestReadAllTornTailMidSector
--- FAIL: TestReadAllTornTailMidSector (12.75s)
    tear_test.go:99: flush [208, 4312), cut at 4304 (in its sector: 208), inside the record [4288, 4312)
        Error:      	Target error should be in err chain:
        	            	expected: "unexpected EOF"
        	            	in chain: "proto: cannot parse invalid wire-format data"
```

## Proof

no: no result of this repository covers etcd's real WAL on files (the WAL extension's examples,
`examples/osfs/walfs`, are models). A proof of the real WAL over the Fs v2 semantics could not use
`NoTear.lean`'s premises: the `PageWriter`'s buffer breaks its program assumption (each write's
buffer at the file offset's in-page offset).

## Notes

- Which cuts fail: `walw tornsim` (`notes/axiom-review/fs-v2-r6/wal/`) built the image a cut at the
  buffer's page boundaries leaves for every flush of a WAL written as etcd does: 194 of 812 (Saves
  of 50-6000 bytes) and 78 of 467 (4100-8000 bytes) fail to open; the others are repaired (a later
  sector of the cut record is all zero) or clean (the cut is at a record boundary).
- The other way to a mid-sector cut, a page rewritten while its previous writeback is in flight on
  a device without stable pages, does not arise in steady state: every rewrite of the tail page
  follows the `fdatasync` of its previous write (0 of 954,493 WAL writes copied into a page under
  writeback). It arises after a restart: `ReadAll`'s unsynced `ZeroToEnd` leaves the tail page
  dirty, and with another process starting writeback 6.5 % of the WAL's writes (about a third of
  the first Saves after a reopen) went into a page under writeback; none of 13,779 such reopens
  logged and scanned left a mixed page on disk. Syncing after `ZeroToEnd` (etcd-io/etcd#22709) removes it.
- A fix for the decoder: a bad last record of the last segment followed only by zeros to the end of
  the file is torn, whatever its sectors hold.
