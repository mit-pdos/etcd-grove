Title: A backend commit can persist a lease checkpoint's consistent index with only some of its leases

### What happened?

With lease checkpoints enabled and persisted, and `--backend-batch-limit=1`:

1. Leases 1 and 2 are granted with a TTL of 600.
2. The member applies entry 3, a lease checkpoint request setting the remaining TTL of both leases to 100.
3. Between the two checkpoints, the backend commits consistent index 3 with remaining TTL 100 for lease 1 and the old 0 for lease 2.

The test below runs these steps (output trimmed):

```
--- FAIL: TestLeaseCheckpointCommittedWithConsistentIndex (0.01s)
        	Error:      	Not equal: 
        	            	expected: []int64{100, 100}
        	            	actual  : []int64{100, 0}
        	Messages:   	remaining TTLs of leases 1 and 2 committed with consistent index 3
```

This can happen on any member persisting lease checkpoints whose backend commits while it applies a checkpoint request for more than one lease.

### What did you expect to happen?

The commit persisting consistent index 3 should also persist lease 2's checkpoint: a member restarting from it does not apply entry 3 again.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestLeaseCheckpointCommittedWithConsistentIndex`](https://github.com/upamanyus/etcd/blob/fix/etcd-apply-lease-checkpoint-sections/server/etcdserver/apply/backend_test.go#L34-L100) on branch [`upamanyus/etcd:fix/etcd-apply-lease-checkpoint-sections`](https://github.com/upamanyus/etcd/tree/fix/etcd-apply-lease-checkpoint-sections), off `main` (22cc5d9ac). On `main` it fails as above.

### Anything else we need to know?

A member that crashes after such a commit and before the next restarts with lease 2's old remaining TTL; if it becomes leader before lease 2's next checkpoint, lease 2 expires late. I did not reproduce a crash and restart.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (22cc5d9ac), unit test only, go1.27.2 linux/amd64.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

`--feature-gates=LeaseCheckpoint=true`, with checkpoints persisted (cluster version 3.6 or later, or `--feature-gates=LeaseCheckpointPersist=true`). The test sets the lessor's `CheckpointPersist` and a backend batch limit of 1, as `--backend-batch-limit=1` does.

</details>
