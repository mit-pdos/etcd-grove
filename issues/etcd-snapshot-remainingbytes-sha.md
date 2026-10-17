---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#18340 issue closed: the comment https://github.com/etcd-io/etcd/issues/18340#issuecomment-2242358927 points out that remaining_bytes leaves out the SHA-256 digest
  - etcd-io/etcd#22066 pr open: counts the digest in RemainingBytes, but also in the loop bound, so the loop never ends (notes/pr-verify/etcd-22066.md)
---

# The snapshot stream's `RemainingBytes` leaves out the 32-byte SHA-256 digest

**Status**: documentation the code contradicts. Nothing in etcd reads `RemainingBytes` (the
client's `Maintenance.Snapshot` reads until `EOF`), so no etcd behavior is wrong, but a client of
the gRPC API that trusts the field stops 32 bytes early and loses the digest that
`etcdutl snapshot restore` checks.

**Where**: `server/etcdserver/api/v3rpc/maintenance.go:197` (`RemainingBytes: uint64(total - sent)`,
fork `goose-lean` 09669450f); the digest response at line 217. `api/etcdserverpb/rpc.proto:753`:
"remaining_bytes is the number of blob bytes to be sent after this message".

**What happens**: every data response's `RemainingBytes` is the database bytes still to come;
the digest, one more 32-byte blob after them, is not counted. On a fresh one-member cluster the
first response has `len(Blob) + RemainingBytes = 28672` and the stream carries 28704 bytes.
Reproduction: `notes/pr-verify/etcd-22066/maintenance_snapshot_remaining_test.go` and
`maintenance_snapshot_test.go` (`TestSnapshotStream`) on branch `pr-verify/etcd-22066`; both fail
at the base on the count.

**Expected**: `RemainingBytes = total + 32 - sent` in each data response (`sha256.Size`), 0 in
the digest's.

**How the proof handles it**: `Snapshot` is not verified (names only in
`Code/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc.toml`). The loop's model
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SnapshotLoopModel.lean` on
`pr-verify/etcd-22066`) proves the base violates the documented property
(`base_not_remainingOk`) and that the fix below meets it (`fixed_remainingOk`).

**Possible fixes**: report `total + int64(h.Size()) - sent` in the data responses and keep the
loop bound `total - sent > 0`. Counting the digest in the bound as well (etcd#22066 at
ab1d5ade8) makes the loop spin forever after the database is sent.

**Found**: 2026-10-17, verifying etcd#22066 (`etcd-pr-verify`).
