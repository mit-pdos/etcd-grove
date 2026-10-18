Title: client/v3: fail Mutex.Lock when its key was recreated while waiting

Two `Mutex` values on one session share one key, and a `Mutex` that finds the key existing takes the key's create revision as its place in the queue ([`tryAcquire`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/client/v3/concurrency/mutex.go#L127-L130)). After waiting for the keys created before that revision, [`Lock`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/client/v3/concurrency/mutex.go#L96-L108) checks only that the key exists, so a key deleted and created again after another session's key passes the check. This PR also checks the create revision, returning `ErrSessionExpired` otherwise, as for a missing key.

Fixes #<issue>

`TestMutexLockKeyRecreated` runs the issue's example; it fails on `main` and passes with this change.

Written with the assistance of generative AI; I reviewed and tested every change.
