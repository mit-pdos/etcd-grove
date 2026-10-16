Title: A lease checkpoint entry can be committed with its consistent index but only some of its checkpoints

### What happened?

With lease checkpoints persisted, a backend commit can persist a lease checkpoint request's consistent index with only some of its checkpoints. In the test below, entry 3 checkpoints leases 1 and 2 to a remaining TTL of 100 with a backend batch limit of 1; the commit persisting consistent index 3 holds remaining TTLs `100` and `0`. This can happen on any member persisting lease checkpoints whose backend commits while it applies a checkpoint request for more than one lease.

### What did you expect to happen?

Every commit persisting consistent index 3 holds both checkpoints (`[]int64{100, 100}`): a member restarting from it does not apply entry 3 again.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestLeaseCheckpointCommittedWithConsistentIndex`](https://github.com/upamanyus/etcd/blob/etcd-apply-lease-checkpoint-sections/server/etcdserver/apply/backend_test.go) on branch [`upamanyus/etcd:etcd-apply-lease-checkpoint-sections`](https://github.com/upamanyus/etcd/tree/etcd-apply-lease-checkpoint-sections). On `main` (b25719d10) it fails (output trimmed):

```
--- FAIL: TestLeaseCheckpointCommittedWithConsistentIndex (0.01s)
        	Error:      	Not equal: 
        	            	expected: []int64{100, 100}
        	            	actual  : []int64{100, 0}
        	Messages:   	remaining TTLs of leases 1 and 2 committed with consistent index 3
```

### Anything else we need to know?

A member that crashes after such a commit, before the next one, restarts with entry 3 applied and lease 2's earlier remaining TTL (here the full TTL); if it becomes leader before lease 2's next checkpoint, lease 2 expires late. I reproduced what the commit persists, not a crash and restart.

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Etcd version (please run commands below)

<details>

`main` (b25719d10), unit test only, Go 1.27.2, linux/amd64.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Lease checkpointing enabled (`--feature-gates=LeaseCheckpoint=true`) with checkpoints persisted (cluster version 3.6 or later, or `--feature-gates=LeaseCheckpointPersist=true`). The test sets the lessor's `CheckpointPersist` and a backend batch limit of 1.

</details>
