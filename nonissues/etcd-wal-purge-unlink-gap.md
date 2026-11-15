---
upstream: none
checked: 2026-11-11
links:
blocks-proof: no
---
# etcd: a power loss during a WAL purge can leave a gap in the WAL files, and the member does not restart

The purge goroutine removes the oldest unlocked WAL files one by one
([`purgeFile`](https://github.com/etcd-io/etcd/blob/6974f522338b/client/pkg/fileutil/purge.go#L76)) and never fsyncs the directory. Under the
bare fsync(2) contract a power loss can make a later removal durable without an earlier one: the
files left are the older one, a gap, then the rest. At the restart `ValidSnapshotEntries` decodes
across the gap, fails the next file's CRC record (`walpb: crc mismatch`), and bootstrap returns an
error: the member stays down.

**Why not an issue:** no test in etcd's own harness (it needs the power-loss model of directory
operations; journaled ext4/xfs keep the removals a prefix). Shown with the WAL crash spec's harness
(W0 `TestCP6Purge`: 190 of 610 posix images fail the restart, 0 under kill -9 and journal
ordering). Liveness only: no state is read wrongly. Fix if wanted: fsync the WAL directory after a
purge round (the W-stages' optional purge fix, skipped by the user, 2026-11-11).

## Proof

no: the restart's error arm (bootstrap returns an error, the member does not start) is allowed by
the restart contract; the WAL crash spec's reader returns `none` for such an image.
