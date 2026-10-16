Title: client/v3: fail Election.Campaign when its key was deleted while waiting

[`Campaign`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/client/v3/concurrency/election.go#L93-L106) waits until every key created before its own under the prefix is deleted, then returns nil without checking that its own key still exists. This PR gets the key after the wait and returns `ErrSessionExpired` unless the key still exists at the create revision `Campaign` waited for, as [`Mutex.Lock`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/client/v3/concurrency/mutex.go#L95-L105) does for its key. `TestElectionWithAuthEnabled` now keeps a waiting campaigner's session alive, since its key expired with the leader's.

Fixes #<issue>

`TestElectionCampaignKeyDeleted` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
