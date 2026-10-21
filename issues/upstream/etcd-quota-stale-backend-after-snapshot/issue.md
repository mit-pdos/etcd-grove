Title: A member that catches up by a snapshot rejects writes with "database space exceeded" while its db is under its quota

### What happened?

In a cluster of members 0, 1 and 2:

1. With no quota set, the cluster stores a 64 KiB value.
2. While member 2 is down, the cluster deletes the key, compacts, defragments members 0 and 1, and takes enough writes that member 2 can only catch up by a snapshot.
3. Member 2 restarts with `--quota-backend-bytes=65536`, below its db's size, and catches up by the leader's snapshot, which is under 64 KiB.
4. A small put through member 2 fails with `etcdserver: mvcc: database space exceeded`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestV3StorageQuotaAfterSnapshot (1.23s)
        	Error:      	Received unexpected error:
        	            	rpc error: code = ResourceExhausted desc = etcdserver: mvcc: database space exceeded
        	Messages:   	put through member 2 with db size 24576 under quota 65536
```

This affects any member whose db was over its quota when it started and that then catches up by a snapshot under the quota, such as a member that was down while the cluster recovered from NOSPACE.

### What did you expect to happen?

The put through member 2 should succeed: member 2's db (24 KiB) is under its quota (64 KiB).

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestV3StorageQuotaAfterSnapshot`](https://github.com/upamanyus/etcd/blob/fix/etcd-quota-stale-backend-after-snapshot/tests/integration/v3_alarm_test.go#L129-L181) on branch [`upamanyus/etcd:fix/etcd-quota-stale-backend-after-snapshot`](https://github.com/upamanyus/etcd/tree/fix/etcd-quota-stale-backend-after-snapshot), off `main` (6782f5229). On `main` it fails as above, in 5 runs of 5.

### Anything else we need to know?

Each rejected put raises a NOSPACE alarm, after which puts through every member fail. Disarming does not help: the next put through member 2 raises the alarm again. Restarting member 2, then disarming, clears it.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (6782f5229), go1.27.2 linux/amd64, through the integration test framework.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Three members, snapshot count 10, snapshot catch-up entries 5; `--quota-backend-bytes=65536` on member 2 after its restart, defaults otherwise.

</details>
