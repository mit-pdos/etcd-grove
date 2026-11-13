---
upstream: none
checked: 2026-11-13
links: []
blocks-proof: no
---

# wal: a segment cut reuses a `N.tmp` left by an interrupted cut without truncating it

The WAL's file pipeline opens `0.tmp`/`1.tmp` without `O_TRUNC`
([file_pipeline.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/file_pipeline.go#L77-L78)).
A member killed (or losing power) in the middle of a segment cut, after the cut wrote its headers into
`0.tmp` (the CRC record, the metadata, the hard state) and before it renamed it
([wal.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/wal.go#L843-L847)),
leaves those headers there. The restarted member's first cut writes its headers over them; when its
hard state encodes shorter (a vote for a member ID, then a higher term with no vote yet), the tail of
the old hard-state record stays after the new headers, durable. A restart that stops right after
that cut reads past the new headers into the stale bytes.

**Why not an issue:** the restart reads the right history. Tested at the fork's pin `0b50f0426` and at
upstream main `1b969e26a2c6` (2026-11-12), go1.27.3/go1.27.4: `TestRestartAfterCutReusesStaleTmp` in
[etcd-wal-cut-reuses-stale-tmp/](etcd-wal-cut-reuses-stale-tmp/) (60 random cases of member IDs,
terms, commits and chain CRCs; interrupted cut, restart, cut into the stale `0.tmp`, stop, restart
as `bootstrap` does: `ReadAll`, `Repair` on `io.ErrUnexpectedEOF`, `ReadAll`) passes: every restart
reads the hard state saved last and all entries, 59 of 60 after a repair that truncates at the end
of the new headers, 1 at a zero length field (EOF). The reason holds for every value, not only those
sampled: the stale bytes are always the tail of the old hard-state frame (the CRC frame is always 16
bytes, the metadata is the same in every incarnation, and a cut appends nothing to its segment before
the rename and the directory fsync), and in a protobuf record no two zero bytes are adjacent. So the
first 8 stale bytes, read as a length field, are either all zero (EOF), or a length of 2^24 or more
(longer than the file: `io.ErrUnexpectedEOF`,
[decoder.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/decoder.go#L110);
or spanning zero sectors), or a shorter one whose five top bytes are padding, so that everything after
it is zeros. In the last two cases the record runs into zeros (a zero tag: it does not parse) and holds an
all-zero sector chunk, so it is torn: `io.ErrUnexpectedEOF`
([decoder.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/decoder.go#L126)).
`Repair` handles it. Bytes written after the cut overwrite the stale ones, and a power loss that
loses them only brings back the same state.

## Proof

no: no fork change. The WAL's crash invariant over `fsExt` has to allow these durable stale bytes
after a reused segment's headers: W1 (no CRC32-C collision on torn data) gets a stale clause, or the
invariant records that the remnant is a suffix of an old hard-state frame, which the decoder always
stops at (`notes/wal-fsext-plan.md`, §2.4 item 6, Q3).

## Notes

The safety rests on the cut's ordering. `TestRestartAfterCutReusesStaleTmpWithRecords` (same file)
builds a state no crash leaves, a `0.tmp` holding old entry records after its headers, with old and
new hard states of the same length: the new headers end on an old frame boundary, the old entry fails
the CRC chain without looking torn, and the restart fails with `ErrCRCMismatch`, which `Repair` does
not handle. A cut that appended before the directory fsync, or a pipeline that preallocated by writing
records, would make that reachable; opening `N.tmp` with `O_TRUNC` (`createNewWALFile(fpath, true)`)
would remove the dependency. Upstream not searched beyond "file_pipeline O_TRUNC" and "0.tmp wal"
(nothing related).
