Title: The leader calls raft's Advance before its apply loop has applied a membership change

### What happened?

When a `Ready` commits a membership change, a follower's raft loop waits for the apply loop to apply it before calling raft's `Advance`; the leader's does not. `TestConfigChangeBlocksApply` run for a leader as well as a follower shows it (output trimmed):

```
--- FAIL: TestConfigChangeBlocksApply (1.01s)
    --- FAIL: TestConfigChangeBlocksApply/StateLeader (0.00s)
        raft_test.go:255: unexpected execution: raft routine should block waiting for toApply
```

This affects every leader that commits a membership change while its apply loop is behind. I have not reproduced a wrong result on a cluster.

### What did you expect to happen?

The leader should call `Advance` only after the membership change is applied, as raft's `Node.Advance` requires of configuration changes and as the follower does.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestConfigChangeBlocksApply`](https://github.com/upamanyus/etcd/blob/fix/etcd-leader-advance-before-applyconfchange/server/etcdserver/raft_test.go#L214-L270) on branch [`upamanyus/etcd:fix/etcd-leader-advance-before-applyconfchange`](https://github.com/upamanyus/etcd/tree/fix/etcd-leader-advance-before-applyconfchange), off `main` (7ff040cb8). On `main` its `StateLeader` case fails as above.

### Anything else we need to know?

Between `Advance` and the apply, the leader's raft accepts a second membership change while it still uses the configuration before the first; on raft alone that lets two different entries commit at the same index.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (7ff040cb8), go1.27.1 linux/amd64; no binaries run.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Any.

</details>
