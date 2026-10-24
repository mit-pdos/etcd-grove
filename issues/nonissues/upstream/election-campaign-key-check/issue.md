Title: Election.Campaign returns nil when its session's lease is revoked or expires while it waits

### What happened?

With elections `e1` and `e2` on the same prefix, on sessions `s1` and `s2`:

1. `e1.Campaign` returns nil: `e1` leads.
2. `e2.Campaign` is called and waits for `e1`'s key to be deleted.
3. While `e2.Campaign` waits, `s2`'s lease is revoked, which deletes `e2`'s key.
4. `e1.Resign` returns nil. Then `e2.Campaign` returns nil, although `e2`'s key is gone: `e2.Leader` returns `election: no leader`, and `e2.Proclaim` returns `election: not leader`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestElectionCampaignKeyDeleted (0.16s)
    election_test.go:138: 
        	Error:      	An error is expected but got nil.
        	Test:       	TestElectionCampaignKeyDeleted
        	Messages:   	e2 elected after its key was deleted
```

This affects any client whose session's lease is revoked or expires while its `Campaign` waits.

### What did you expect to happen?

`e2.Campaign` should return an error, since `e2`'s key was deleted and `e2` is not the leader.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestElectionCampaignKeyDeleted`](https://github.com/upamanyus/etcd/blob/fix/election-campaign-key-check/tests/integration/clientv3/concurrency/election_test.go#L107-L139) on branch [`upamanyus/etcd:fix/election-campaign-key-check`](https://github.com/upamanyus/etcd/tree/fix/election-campaign-key-check), off `main` (22cc5d9ac). On `main` it fails as above.

### Anything else we need to know?

If an election `e3` on a third session campaigns after step 3 and before step 4, `e3.Campaign` and `e2.Campaign` both return nil, so two campaigners act as leader at once.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (22cc5d9ac), `go test` with go1.27.2 linux/amd64; no `etcd` or `etcdctl` binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The integration test's single-member cluster, defaults.

</details>
