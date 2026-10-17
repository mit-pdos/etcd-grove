---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#21128 issue open: this bug (key left after `etcdserver: mvcc: required revision has been compacted` in `Campaign`)
  - etcd-io/etcd#21165 pr open: the fix (always `Resign` when the wait fails); verified on branch `pr-verify/etcd-21165`
---

# Election.Campaign leaves its key in etcd when the wait fails with the context live

**Status**: a bug. When `Campaign`'s wait for older keys fails while the caller's context is not
done, `Campaign` returns the error but leaves its key in etcd, held by the session's lease, and
makes a later `Resign` a no-op. The election stays blocked for every other candidate until the
session ends.

**Where**: `client/v3/concurrency/election.go:93-102` at the pinned revision (`etc/goose.py`,
etcd `09669450f`):

```go
	err = waitDeletes(ctx, client, e.keyPrefix, e.leaderRev-1)
	if err != nil {
		// clean up in case of context cancel
		select {
		case <-ctx.Done():
			e.Resign(client.Ctx())
		default:
			e.leaderSession = nil
		}
		return err
	}
```

and `Resign` (line 133), which returns nil at once when `leaderSession` is nil.

**What happens**: `waitDeletes` fails with the context still live, for example with
`ErrCompacted` from its watch, a `Get` error, or a closed watch channel. `Campaign` takes the
`default` branch: it clears `leaderSession`, keeps `leaderKey`, and returns the error. The key it
created (or reused) at line 79 stays under the prefix, attached to the session's lease. If its
create revision is the lowest, it is the leader: `Leader` returns it and every other `Campaign`
on the prefix waits behind it. The caller cannot clean up: `Resign` returns nil without deleting
anything (`leaderSession == nil`). Only `Session.Close` (or the lease expiring) removes the key,
and that also removes every other key of the session.

Reproduction: `TestElectionCampaignCleanupOnWaitDeletesError` of etcd-io/etcd#21165
(`tests/integration/clientv3/concurrency/election_test.go` at the PR head `3982e162e`) injects a
compacted watch response. It fails at the pinned code (the fork's `goose-lean` without the PR's
change) and passes with it (`notes/pr-verify/etcd-21165/README.md` on branch
`pr-verify/etcd-21165`).

**Expected**: on an error, `Campaign` either removes its key (as it already does when the context
is done, and after a failed `Proclaim`) or keeps `leaderSession` so the caller can `Resign`. The
issue asks for one of the two.

**How the proof handles it**: on `lean`, `Election.Campaign.spec`'s error case
(`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Campaign.lean`) is only "some state", so it
says nothing about the key. On `pr-verify/etcd-21165`, the error case is strengthened (Resign ran,
the key is gone unless the delete failed) and proved of the PR's code.

**Possible fixes**: call `Resign(client.Ctx())` on every wait error (etcd-io/etcd#21165), or keep
`leaderSession` (and `leaderKey`) on the error so that the caller's `Resign` deletes the key.

**Found**: 2026-10-17, while verifying etcd-io/etcd#21165 (the bug was already reported upstream
as etcd-io/etcd#21128).
