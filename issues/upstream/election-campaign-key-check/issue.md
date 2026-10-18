Title: Election.Campaign returns nil after its session's lease was revoked while it waited

### What happened?

With `e1` the leader and `e2.Campaign` waiting behind `e1`, revoking the lease of `e2`'s session and then `e1.Resign` make `e2.Campaign` return nil, although `e2` is not the leader:

```go
e1.Campaign(ctx, "e1")    // e1, e2 on sessions s1, s2, same prefix
go e2.Campaign(ctx, "e2") // waits for e1
cli.Revoke(ctx, s2.Lease())
e1.Resign(ctx)
```

Each call's result, in order, at `main`, then `e2.Proclaim` and `e2.Leader` after `e2.Campaign` returns:

```
e1.Campaign: <nil>
cli.Revoke(s2.Lease()): <nil>
e1.Resign: <nil>
e2.Campaign: <nil>
e2.Proclaim: election: not leader
e2.Leader: election: no leader
```

The same happens for any `Campaign` whose key (`Key()`) is deleted while it waits, as when its session's lease expires.

### What did you expect to happen?

`e2.Campaign` returns an error, since `e2`'s key no longer exists and `e2` is not the leader.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestElectionCampaignKeyDeleted`](https://github.com/upamanyus/etcd/blob/fix/election-campaign-key-check/tests/integration/clientv3/concurrency/election_test.go) on branch [`upamanyus/etcd:fix/election-campaign-key-check`](https://github.com/upamanyus/etcd/tree/fix/election-campaign-key-check), which runs the calls above. On `main` (b25719d10) it fails:

```
--- FAIL: TestElectionCampaignKeyDeleted (0.26s)
    election_test.go:137: 
        	Error:      	Expected error with "mutex: session is expired" in chain but got nil.
        	Test:       	TestElectionCampaignKeyDeleted
        	Messages:   	e2 elected after its key was deleted
```

### Anything else we need to know?

If a third campaigner `e3` (session `s3`) campaigns after the revoke and before `e1.Resign`, `e3.Campaign` and `e2.Campaign` both return nil, so code that acts on `Campaign` returning nil runs with two leaders.

#11051 and #11777 reported the same bug and were closed as stale.

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Etcd version (please run commands below)

<details>

`main` at b25719d10cdc41fb707b0d9f819c2529dec5d590, `go test` with go1.27.2 linux/amd64; no `etcd` or `etcdctl` binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The integration test's single-member cluster, defaults.

</details>
