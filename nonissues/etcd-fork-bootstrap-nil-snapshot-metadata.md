---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# etcdserver (the Goose fork only): `bootstrap` dereferences a nil snapshot `Metadata` when the WAL has no snapshot record

In the fork that this repository verifies (upamanyus/etcd at `a4d2bb172`, the `etc/goose.py` pin, whose
raftpb messages are protobuf-go v2 with pointer fields), `bootstrap`'s restart branch builds a snapshot
from scratch when the WAL gave none: `sn = &raftpb.Snapshot{}`, then `sn.Metadata.ConfState = &cs`
(`server/etcdserver/bootstrap.go:108-114`). `Metadata` is a nil `*SnapshotMetadata` there, so the
assignment panics.

**Why not an issue:** unreachable as etcd uses the code, and only in the fork. `s.wal.snapshot` is nil
only if `recoverSnapshot` found no valid snapshot record (`wal.ValidSnapshotEntries` empty,
`bootstrap.go:448-470`). Every WAL starts with the index-0 snapshot record that `wal.Create` writes
(`server/storage/wal/wal.go:180`), and that record is always valid. Upstream etcd's gogoproto
`Snapshot.Metadata` is a value, not a pointer, so upstream has no nil dereference here. Found by code
reading (the restart S4 Freeze review, 2026-11-12); no test.

## Proof

no: `bootstrap` is names-only, behind the restart contract (`bootstrapRestartContract`), and the
contract's image always has a WAL with its snapshot records. Building `sn.Metadata` (or keeping the
`nil` check out of the branch) on the fork would remove the dead panic.

## Notes

Found by the `spec-reviewer` of restart S4's Freeze package and confirmed by reading the fork at
`a4d2bb172`.
