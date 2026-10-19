Title: client/v3: fail Election.Campaign when its key was deleted while waiting

[`Campaign`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/client/v3/concurrency/election.go#L93-L106) waits until every key created before its own under the prefix is deleted, then returns nil, assuming its own key still exists. If the session's lease is revoked or expires during the wait, that key is gone, and `Campaign` returns nil although the campaigner is not the leader. This PR gets the key after the wait and returns `ErrSessionExpired` unless it still exists at the create revision `Campaign` waited for, as [`Mutex.Lock`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/client/v3/concurrency/mutex.go#L96-L104) does.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass. The first commit also stops orphaning the sessions that `TestElectionWithAuthEnabled` elects second: that test passed only because of this bug.

Written with the assistance of generative AI; I reviewed and tested every change.
