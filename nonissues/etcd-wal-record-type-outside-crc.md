---
upstream: none
checked: 2026-11-13
links:
  - etcd-io/etcd#22709 issue open: related, different: ReadAll's ZeroToEnd is not synced, which leaves the stale bytes under a new frame that the upstream case below needs
blocks-proof: yes
---

# wal: a power loss that tears only a record's one-byte Type turns it into another record type with a valid CRC

A WAL record's CRC covers its `Data` only, not its `Type`
([encoder.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/encoder.go#L73-L74),
[decoder.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/decoder.go#L133-L138)).
If a power loss keeps every byte of an unsynced frame but its Type value (frame byte 9), and the
byte under it before the write was another record type, the restart accepts the frame as a record
of that type with the intended `Data`: an entry read as a `HardState` (entry `{Type, Term, Index}`
parses as `{Term, Vote, Commit}`), a hard state read as an entry (it replaces the entry at index
`Commit`), either read as a snapshot record. Under a zero byte (the preallocated or zeroed tail) the
record has Type 0, and the restart fails with "unexpected block type 0", which bootstrap does not
repair.

**Why not an issue:** no real crash image; it needs a tear of one byte inside an aligned 8-byte word
(bytes 8-15 of a frame hold the Type tag, the Type and the start of the CRC field), which the
measured tear mechanisms on configuration C (a copy cut short at a source page boundary, which keeps
a prefix of the write; pages written back independently, at 4 KiB boundaries) do not leave. It is
allowed by the per-byte crash model of `GooseLang/Ext/Fs` ("Byte-level crash candidates").
Shown on constructed images at the fork's `f15d88841` and at upstream main `1b969e26a2c6`
(2026-11-12), go1.27.3, tests in [etcd-wal-record-type-outside-crc/](etcd-wal-record-type-outside-crc/):

- `TestWALTypeTearStale` (upstream and the fork): the last unsynced frame is the hard state
  `{1,1,2}`, its Type byte left as a stale `0x02` (upstream: ReadAll's zeroing lost,
  `nonissues/etcd-wal-readall-zero-unsynced.md`). The restart succeeds with entry 2, synced and
  committed (normal, 40 bytes), replaced by `Entry{ConfChange, Term 1, Index 2}` with no data, and
  entry 3 dropped.
- `TestWALTypeTearStaleTmp` (the fork, which syncs the zeroing): after an interrupted cut, the next
  cut writes shorter headers over the reused `0.tmp`
  (`nonissues/etcd-wal-cut-reuses-stale-tmp.md`); when the old hard state's vote is a 10-byte member
  ID, the new headers' CRC field encodes in 4 bytes and the old commit's last byte is 3 or 5, the
  remnant's byte under the next entry frame's Type is a state or snapshot type. Keeping all of the
  next Save but that byte: the entry is read as `HardState{term 0, vote = its term, commit = its
  index}` (then overridden by the Save's own state record, the entry lost) or as a snapshot record
  (`ErrSnapshotMismatch`). 3 instances found among 36 candidate hard states of 2·10^6 tried.
- `TestWALTypeTearZero`: the same tear over a zero byte: `ReadAll` fails, "unexpected block type 0".

`TestWALByteMix` enumerates the mixes (below); no other mechanism accepts wrong content without a
CRC-32C collision.

## Proof

yes: W1 (`LinuxFs/.../wal/W1.lean`, a world premise) excludes these crashes, and the CRC evidence
does not justify that for the Type byte. Narrowing W1 to `Data` (below) needs the fork's `alloc` to
open `N.tmp` with `O_TRUNC` (then every byte under a fresh frame is zero and a torn Type is 0, an
error every read spec allows), or a second premise on the Type byte.

## Notes

**The enumeration** (`TestWALByteMix`, `-short`, the fork): 25 WALs from real
`Create`/`Save`/`SaveSnapshot` sequences (entries of 0-700 bytes, nil/normal/conf-change types,
state-only Saves, snapshots), the last k = 1..3 frames unsynced; old bytes zero, or a stale stream
with the same synced prefix at the same offsets (`stale+0`) or shifted by 8-40 bytes; exhaustive
over the differing non-`Data` bytes (in windows of 12 when more), the cut points, and 1000 random
mixes per case (20000 without `-short`): 8,563,550 images through the restart bootstrap does
(`ValidSnapshotEntries`, `Open` at the newest valid snapshot, `ReadAll`, `Repair` on
`io.ErrUnexpectedEOF`, `ReadAll`), in memory with the real decoder and `ReadAll`; 1,716 sampled
images re-run on real files agree. Results:

- **old = zero** (the fork's tail: fallocate, and ZeroToEnd synced by F-Z): 884,796 images, 0 accepted
  with wrong content; 592 accept a Type-0 record in the decoder and fail in `ReadAll`. A zero-only run without `-short` (`BYTEMIX_OLD=zero BYTEMIX_BITS=18`: exhaustive per frame up to 18 bits, 20000 random mixes per case): 2,671,002 images, 0 wrong, 7,121 Type-0 failures, 535 real-file cross-checks agree.
- **stale+0**: 808 wrong (Type tears, as above) besides 4,954 that the stale stream alone explains
  (the lost-zeroing case). **stale-shifted**: 50 wrong (a hard state read as a snapshot record).
- `TestWALByteMixStaleTmp` (the real reused-`0.tmp` state, 60 random cases, 365,760 images): 0 wrong
  (the instances need the alignment `TestWALTypeTearStaleTmp` searches for).

**Why zero old bytes are safe, for every value** (given no CRC-32C collision on `Data`): each byte
of the frame is either the intended byte or 0. If the accepted record's `Data` is the intended one,
its `Crc` must be `crc(chain, Data)`, the intended value; its Type field (a one-byte varint, 1-5) is
the intended one or 0 (unknown type: `ReadAll` and `Verify` fail; `ValidSnapshotEntries` skips it, but
bootstrap's `ReadAll` then fails). A zeroed tag byte is field 0, which does not parse. A zeroed length
byte gives a shorter frame, whose record is a truncation (a parse error or a different `Data`, so a
CRC mismatch) or ends at the length word (0: a clean stop); a zeroed padding flag reads the padding as
the next length word, whose low bytes are zero (a stop or a length past the file). So any acceptance
with wrong content is a different `Data` with a matching CRC field: a collision.

**The narrowest premise this justifies** (with `O_TRUNC`, so old bytes are zero): *every frame the
decoder accepts in a crash image carries the `Data` of the record written at that position of the
stream* (no CRC-32C collision on a torn frame); the frame's other bytes then follow from the zero-old
invariant. Without `O_TRUNC`, add: *in a frame the decoder accepts, the aligned 8-byte word holding
the Type (frame bytes 8-15) comes back whole, as written or as before* (a stale Type then comes with a
stale CRC field, which matches the intended `Data`'s CRC only by collision).
