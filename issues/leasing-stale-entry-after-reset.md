---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#19091 issue closed: related, not this bug (our report: stale cached Get after the session lease expires, from the non-blocking session.Done check); closed by the stale bot
  - etcd-io/etcd#19092 pr closed: related, not this bug (our fix for #19091); closed unmerged
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: no
---

# clientv3/leasing: a key read just before the leasing session expires keeps serving its old value after other clients write it

If the leasing KV's session lease ends (expires, or is revoked) between the moment a `Get`
acquires a key and the moment it caches it, the key is cached under the next session anyway. Other
clients then write the key without revoking anything, since the key's leasing record went away
with the old lease, and the leasing KV's `Get` keeps returning the old value until the next session
reset.

**Expected:** after another client's write commits, the leasing KV should not return the old
value, as the package "serves linearizable reads from a local cache"
([doc](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/doc.go#L15-L18)).

**Impact:** users of `client/v3/leasing` whose session lease expires (a keep-alive that does not
get through in time, a partition, a paused process) while a `Get` of an uncached key is in flight;
a narrow window, but the stale value then persists for the whole next session, with no error.

**Reproduction:** `TestLeasingSessionExpireAfterAcquire` in
[`issues/leasing-stale-entry-after-reset/leasing_session_expire_after_acquire_test.go`](leasing-stale-entry-after-reset/leasing_session_expire_after_acquire_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (the leasing KV's
client `KV` is wrapped to revoke the session lease, as an expiry would, right after the acquisition
commits, and to wait for the new session):

```
$ go test ./integration/clientv3/lease -run '^TestLeasingSessionExpireAfterAcquire$' -count=1
--- FAIL: TestLeasingSessionExpireAfterAcquire (6.17s)
        	Error:      	Condition never satisfied
        	Messages:   	expected the leasing KV to return the value put by another client
FAIL
```

**Cause:** [`get`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L323-L336)
caches the key (`leases.Add`) after `acquire` commits, even if
[`monitorSession`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L138-L145)
reset the cache in between. [`monitorLease`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L174-L185)
skips every event that is not a `"REVOKE"` put, including the leasing key's delete, so nothing
evicts the entry.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the leasing KV's intended spec is false here; the proof's facts are about the acquisition
revision and `leasingX` has no "entries carry the current lease" invariant
(`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean`); the verified fork carries no fix.

## Fix

**Branch**: `leasing-stale-entry-after-reset` (upamanyus/etcd, pushed): 3d0769edc test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/leasing: release a key when its leasing key is deleted

`get` acquires a key with a transaction that puts the leasing key `pfx+key` under the current
session's lease, then caches the response and starts `monitorLease`. If the session's lease ends
between the commit and `Add`, etcd deletes the leasing key with the lease and `monitorSession`
resets the cache and starts a new session, but `Add` then caches the key anyway. Nothing evicts it
before the next reset: `monitorLease` skips every event that is not a `"REVOKE"` put, the delete
included; other clients' writes are guarded only by the leasing key, which no longer exists; and a
`"REVOKE"` put would carry the old lease, not the new session's.

This PR makes `monitorLease` rescind the key when it sees the leasing key's delete, as it already
does when its `Get` finds the leasing key gone. `rescind` evicts the entry; its guarded delete of
the leasing key does nothing if the key is gone or was acquired again since. The integration test
revokes the session lease after the acquisition commits and before the key is cached, waits for
the new session, puts a new value with another client and checks that the leasing KV returns it.

Alternative: never cache an entry acquired under a lease that is no longer the session's (record
the session's lease ID in the cache under its lock; `Add` refuses a mismatch). It closes the
window entirely, at about four times the change.
