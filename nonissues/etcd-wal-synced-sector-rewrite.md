---
upstream: none
checked: 2026-11-11
links:
blocks-proof: no
---
# etcd: the WAL silently loses synced records if the device can corrupt a synced sector when the sector is written again

The WAL appends records into a partly written sector after an `fdatasync`, so the device rewrites
a sector that holds synced bytes. If a power loss during that rewrite can leave the sector
garbled, synced bytes included, the restart's decoder can see a garbled record length that runs
past the end of the file, which it reports as a torn tail (`io.ErrUnexpectedEOF`). Bootstrap then
calls `Repair` ([repair.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/repair.go#L32)), which truncates the file there,
and the retried read succeeds without the synced records after that point and without an error:
entries and hard states that raft was told were durable are gone.

**Why not an issue:** it depends on a device behavior that etcd, like most storage software,
assumes away: that rewriting a sector never corrupts the bytes of it that were already durable
(sector writes atomic with respect to those bytes; unsynced bytes may come back arbitrary). The WAL
cannot tell a garbled synced record from a torn unsynced one: it does not record the last synced
offset. Found by the WAL robustness tester (W1.5, chain 9030, posix with the weaker sector model):
the restart read `base 28@3, hs 4/2/36` where every possible history's synced prefix ended with
`snap34` and `hs 4/2/38`, without an error. The path through `Repair` is the likely one,
not confirmed on the pre-repair image (`/shared/tmp/wal-spec/w15-report.md` §3.3).

## Proof

no: the WAL's crash spec rests on the world assumption the user adopted on 2026-11-11
(`notes/decisions.md`, "WAL W3"): rewriting a sector never corrupts the bytes of it that were
already synced; unsynced bytes are arbitrary; no CRC32 collision on torn data. This file records
the WAL's dependence on it. A fork fix (`Repair` refusing to truncate before the last synced
offset) would need the WAL to record that offset.
