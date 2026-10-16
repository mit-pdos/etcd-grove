Title: server/lease: persist a lease checkpoint entry in one batch transaction

When lease checkpoints are persisted, [`applierV3backend.LeaseCheckpoint`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/apply/backend.go#L99-L107) calls [`lessor.Checkpoint`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/lease/lessor.go#L367-L383) once per lease, and each call writes its lease in its own [section of the batch transaction](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/lease/lease.go#L55-L61). [The post-lock hook](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/server/etcdserver/server.go#L2448-L2455) sets the consistent index to the entry at each section, so a backend commit between two sections persists the entry's index with only the first leases. This PR makes `Lessor.Checkpoint` take the request's checkpoints and write them in one section.

Fixes #<issue>

`TestLeaseCheckpointCommittedWithConsistentIndex` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
