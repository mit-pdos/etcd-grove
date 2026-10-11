# Election.Campaign returns nil after its key was deleted while it waited

## Summary

`Election.Campaign` (`client/v3/concurrency/election.go`) returns nil as soon as all keys created before its own are gone, without checking that its own key still exists. If the key is deleted while `Campaign` waits (the session's lease is revoked or expires, the session is closed, or another `Election` on the same session and prefix resigns), `Campaign` reports leadership while another campaigner is the leader, and both campaigns return nil. `Mutex.Lock` has had the corresponding check since b14c7cd44. Found while formally verifying the concurrency package.

## What happens

At f061acd09, in `Campaign`:

- lines 73-90 create the key `keyPrefix/<lease>`, or, if it exists (another `Election` on the same session and prefix), reuse it and its create revision as `e.leaderRev` and proclaim the new value over it;
- line 93 waits, with `waitDeletes(ctx, client, e.keyPrefix, e.leaderRev-1)`, until every key under the prefix created before `e.leaderRev` is deleted;
- lines 104-106 set `e.hdr` and return nil.

Nothing checks that the key at `e.leaderRev` is still there when `waitDeletes` returns. If it was deleted during the wait, another campaigner whose key was created later is now the first-created key, and its `Campaign` returns nil too. For the stale campaigner, `Leader()` names the other key and `Proclaim` fails with `ErrElectionNotLeader`; code that acts on `Campaign`'s return alone runs with two leaders.

The key can be deleted during the wait with the caller's context live:

- another `Election` on the same session and prefix resigns, e.g. because its own `Campaign` was canceled (lines 96-98 call `Resign`), since both elections share the key `keyPrefix/<lease>`;
- the session's lease is revoked or expires, or the session is closed.

## How to reproduce

The test `tests/integration/clientv3/concurrency/election_campaign_test.go` on the branch below (`go test -race -run TestElectionCampaign ./integration/clientv3/concurrency/` from `tests/`) fails on `main` in both schedules:

- Shared session: C (session T) leads. A (session S) campaigns and waits behind C; B, also on session S and the same prefix, finds A's key, proclaims its own value over it, and waits. A's `Campaign` is canceled, so it resigns and deletes the shared key. D (session U) campaigns and waits. When C resigns, D's `Campaign` returns nil and D is the leader, and B's `Campaign` returns nil as well, although its key no longer exists.
- Revoked lease: C (session T) leads. A (session S) campaigns and waits. S's lease is revoked, deleting A's key. D (session U) campaigns and waits. When C resigns, both D's and A's `Campaign` return nil.

On `main`:

```
B: Campaign returned nil; Key()=/election-campaign-shared/6dbfa123ec4b1b03 Rev()=3; key exists at that revision: false; Leader()="/election-campaign-shared/6dbfa123ec4b1b07" (err <nil>); Proclaim: election: not leader
--- FAIL: TestElectionCampaignSharedSessionKeyDeleted
A: Campaign returned nil; Key()=/election-campaign-revoked/6dbfa123ec4b1b25 Rev()=10; key exists at that revision: false; Leader()="/election-campaign-revoked/6dbfa123ec4b1b29" (err <nil>); Proclaim: election: not leader
--- FAIL: TestElectionCampaignLeaseRevoked
--- PASS: TestElectionCampaignSeparateSessionsKeyKept
```

The third test runs the shared-session schedule with B on its own session, as a control.

## Expected

The `Campaign` doc comment:

> Campaign puts a value as eligible for the election on the prefix key. Multiple sessions can participate in the election for the same prefix, but only one can be the leader at a time.

A `Campaign` whose key is gone is no longer a candidate, so it should return an error rather than nil.

## Proposed fix

Branch `election-campaign-key-check`: after `waitDeletes`, `Campaign` gets its key, as `Mutex.Lock` has done since b14c7cd44 ("concurrency: make lock more reliable"):

- on a `Get` error, it cleans up as the existing `waitDeletes` error path does;
- if the key is gone, it resets the leader state as `Resign` does and returns `ErrElectionNotLeader`;
- if the key exists with another create revision (deleted and recreated under the same session by a sibling `Election`), it adopts that revision and waits again, as the sibling fix to `Mutex.Lock` does (branch `mutex-lock-recreated`);
- on success, `e.hdr` is the `Get`'s header, the revision at which leadership was confirmed.

Alternatives for the error: reusing `ErrSessionExpired`, as `Mutex.Lock` does, but its message is "mutex: session is expired" and the key can be lost with the session alive (a sibling `Election` resigning); or a new `ErrElectionKeyLost`, which adds API for a condition `ErrElectionNotLeader` already names (`Proclaim` returns it when the leader key is gone).

`TestElectionWithAuthEnabled` relied on the bug: it orphans every session (TTL 10), so client1's second campaigner's key expires together with the first campaigner's, and its `Campaign` returned nil anyway. The branch keeps the second campaigners' sessions alive instead.

## Also noticed

- `ResumeElection` uses `pfx` as the key prefix as given, while `NewElection` appends `/`: is a resumed election's `Leader()`/`Observe` meant to range over `pfx` without the `/` (so that it also matches, e.g., `pfx2/...`)?
- After a failed `Proclaim`, `leaderKey` is set to `""` while `leaderSession` stays set, so a later `Proclaim` or `Resign` transacts on the key `""`: should it also clear `leaderSession`, as `Resign` does?
