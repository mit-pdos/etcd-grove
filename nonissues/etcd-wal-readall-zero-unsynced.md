---
upstream: none
checked: 2026-11-11
links:
  - etcd-io/etcd#19095 pr merged: related, different (ReadAll returns the continuous entries with ErrSliceOutOfRange, for the robustness reader)
blocks-proof: yes
---
# etcd: after a power loss, a restarted member can read WAL records its current history never wrote

When a member restarts after a power loss that tore the WAL's tail, `ReadAll` zeroes the file
past the last valid record but does not sync the zeroing. If the member then appends a record that
is byte-identical to the stale one at that offset (a leader re-sending the entries the member lost)
and power fails again before the next sync, the new record can survive while the zeroing does not:
the stale records after it pass the CRC chain, and the next restart reads a hard state from the
previous incarnation that the current one never saved.

**Why not an issue:** no test in etcd's own harness: reaching it needs a power-loss model of the
file system (unsynced pages written back out of order), which neither etcd's tests nor its
failpoints have. Shown with the WAL crash spec's ptrace record-and-replay harness (W0
`TestCP5Prime`; W3 `TestW3FZ` in [etcd-wal-readall-zero-unsynced/](etcd-wal-readall-zero-unsynced/),
against the real code with no modelled fix): at the fork's `a4d2bb172`, 4 of 1230 posix/ordered
crash images of the second incarnation read `hs{1,1,1}` with entries 1..3 where the history saved
`hs{1,1,3}` (a record of no crash image of the current history); at `71f99a4bf`, 0 of 1312. Raft-level harm
is not shown (the stale record was never synced, so never acted on), but every crash relation of
the form "a prefix of what this incarnation's history wrote" is false. Code:
[`ReadAll`'s `ZeroToEnd`](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L571),
[`ZeroToEnd`](https://github.com/etcd-io/etcd/blob/6974f522338b/client/pkg/fileutil/fileutil.go#L101) (truncate and fallocate, no sync). The
same at upstream main (6974f522338b, 2026-11-10).

## Proof

yes: the WAL's crash spec (the W-stages, `/shared/tmp/wal-spec/scope.md` "C-P5'") states the
restart's image as a record prefix of the history, at or past the synced mark; without the fix that
is false. The fork's `goose-lean-walsync` 41fddbc2d (`etc/goose.py`) fdatasyncs the tail after
`ZeroToEnd`, which also makes every restart's image durable.

## Fix

**Branch**: `fix/etcd-wal-readall-zero-unsynced` in `/shared/tmp/wal-spec/w3/upstream-etcd`
(not pushed): 25220423f fix (no in-tree test: durability is not observable without a power-loss
model; the regression test is the harness's `TestW3FZ`)
**Base**: etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d

**PR draft**:

Title: wal: fdatasync the zeroed torn tail in ReadAll

ReadAll in write mode zeroes the tail past the last valid record
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L571)) so that a torn write's leftover records cannot follow
new ones, but the zeroing is not synced. After a power loss that keeps a record appended at that
offset but not the zeroing, the stale records after it come back, and pass the CRC chain when the
new record is byte-identical to the stale one there. This PR fdatasyncs the tail after
`ZeroToEnd`.

## Notes

Upstream not searched beyond the related PR above. The commit needs a `Signed-off-by` before filing.
