---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#13508 pr merged: related, not this bug (adds --experimental-enable-lease-checkpoint-persist, the persistence whose atomicity fails here)
  - etcd-io/etcd#17132 issue closed: related, not this bug (TTLs reset on restart because checkpoints were not persisted at all)
blocks-proof: no
---

# server: a lease checkpoint entry is not persisted atomically with its consistent index

When checkpoints are persisted (cluster version 3.6+, or `--experimental-enable-lease-checkpoint-persist`),
applying a `LeaseCheckpoint` entry writes each lease in its own critical section of the backend's
batch transaction, so a backend commit between two of them persists the entry's consistent index
with only some of its checkpoints. After a crash in that window the entry is not re-applied, and
the other leases are recovered with an older (larger) remaining TTL: they live longer than their
TTL.

**Why not an issue:** not a guarantee etcd makes: a lease may outlive its TTL (every leader change
did this before checkpoints were persisted, #17132); a client is only promised the lease is not
revoked before its TTL, and the lost checkpoint can only lengthen a lease, never shorten it.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; `applierV3backend.LeaseCheckpoint`'s triple takes a request with at most one checkpoint
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/applierV3backend__LeaseCheckpoint.lean`), a
premise etcd does not meet (the lessor batches up to 1000); today the workload has no leases
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`).

## Notes

- The test,
  [`nonissues/etcd-apply-lease-checkpoint-sections/checkpoint_index_test.go`](etcd-apply-lease-checkpoint-sections/checkpoint_index_test.go)
  (`server/etcdserver/apply`, through `newApplierV3Backend` with the server's post-lock hook and a
  batch limit of 1), fails at etcd-io/etcd@1573d5941 (go1.27.3): lease 2's remaining TTL is `0`
  (not checkpointed) in a commit that persists consistent index 3. It shows the broken atomicity of
  an entry with its consistent index, which `txPostLockInsideApplyHook` (#13766) is meant to give.
- The 2026-10-23 review's plan: not a wrong result (a lease kept alive longer is safe); skip for now
  rather than non-issue, as a possible liveness improvement. Under the issues/nonissues split it
  goes here.
- Fix branch `fix/etcd-apply-lease-checkpoint-sections` (upamanyus/etcd, pushed, never filed):
  9dc872522 test, 60d7c705e fix, off etcd-io/etcd@22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4.
  `Lessor.Checkpoint` takes the request's checkpoints and persists them under one
  `LockInsideApply` (an interface change; `FakeLessor` and `etcdutl`'s `SimpleLessor` updated).
