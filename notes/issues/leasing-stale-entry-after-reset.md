# clientv3/leasing: a key acquired just before a session ends stays cached under the next session

## Summary

If the leasing KV's session lease ends (expires, or is revoked) between the commit of a key's acquisition and the moment the key is cached, the key is cached anyway. Nothing evicts it until the next session reset. Meanwhile other clients write the key without revoking anything, because the leasing key went away with the lease, and the leasing KV's `Get` keeps returning the old value. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `get` (`client/v3/leasing/kv.go:301-338`) acquires the key with `acquire` (`kv.go:265-299`). Its transaction puts the leasing key `pfx+key` with `WithLease(lkv.leaseID())`, the current session's lease (`kv.go:276`). On success `get` caches the response (`leases.Add`, `kv.go:330`) and starts `monitorLease` for the key.
2. Suppose the session's lease ends after the acquisition commits and before `Add`. etcd deletes the leasing key along with the lease. `monitorSession` (`kv.go:129-157`) sees the session end, resets the cache (`kv.go:144`) and starts a new session. `Add` then caches the key anyway, after the reset.
3. `monitorLease` (`kv.go:159-188`) watches the leasing key from the acquisition, but it skips every event that is not a `"REVOKE"` put (`kv.go:177-179`), the leasing key's delete included. So it never evicts the entry.
4. Other clients' writes of the key are guarded by `CreateRevision(pfx+key) < rev+1`, which holds because the leasing key no longer exists. They commit without revoking anything. And a `"REVOKE"` put would keep the old lease, which is not the new session's, so `monitorLease` would return without rescinding (`kv.go:180`).
5. The entry stays until the next session reset, and the leasing KV's `Get` returns its stale value.

The session's lease can end like this through an expiry: a keep-alive that does not get through in time, a partition, or a paused process.

## How to reproduce

The branch below adds `TestLeasingSessionExpireAfterAcquire` (`tests/integration/clientv3/lease/leasing_test.go`):

- The leasing KV's client has its `KV` wrapped to run a hook after the first transaction commits, which is the acquisition of `k`.
- The hook revokes the session lease (as an expiry would) and waits until the leasing KV has granted a new lease. It grants one only after it has reset its cache.
- Another client then puts `k = "v2"`, and the test checks that the leasing KV eventually returns `"v2"` (within 5 s).

On `main` it keeps returning `"v1"`:

```
Condition never satisfied
expected the leasing KV to return the value put by another client
```

```
cd tests && go test ./integration/clientv3/lease/ -run TestLeasingSessionExpireAfterAcquire -v
```

No existing test encodes the old behaviour; the suite passes unchanged with the fix.

## Expected

A key whose leasing key is gone is not served from the cache, as when the whole session ends.

## The fix

Branch `leasing-stale-entry-after-reset` (one commit, with the test). `monitorLease` rescinds the key when it sees the delete of the leasing key. It already does this when its `Get` finds the leasing key gone (`kv.go:169`). `rescind` evicts the entry, and its guarded delete of the leasing key does nothing if the key is gone or was acquired again since. This is a five-line change. It also covers a leasing key deleted any other way, for example by hand.

The alternative is to never cache an entry acquired under a lease that is no longer the session's:

- `monitorSession` records the current session's lease ID in the cache, under the cache's lock, when it resets the cache and when it installs the new session;
- `acquire` returns the lease ID it used;
- `Add` refuses the entry (still filtering the response by the `Get`'s options) if that ID differs.

This closes the window entirely: the entry is never installed. With the fix above, the entry is installed and then evicted as soon as the watch delivers the leasing key's delete. That window is like the one that already exists when a session expires: the cache serves until the keep-alive notices. The alternative touches `monitorSession`, `acquire`, `get` and `Add`, about four times the change.
