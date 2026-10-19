Title: client/v3: fail Mutex.Lock when its key was recreated while waiting

`Mutex` values on one session share one key; a `Mutex` that finds the key already there takes its create revision as its place in the queue ([`tryAcquire`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/client/v3/concurrency/mutex.go#L127-L130)). After waiting for the keys created before that revision, [`Lock`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/client/v3/concurrency/mutex.go#L96-L108) checks only that the key exists, not that its create revision is still the one waited on. If another `Mutex` on the session deleted the key and created it again after another session's key, `Lock` returns while that session holds the lock. This PR also checks the key's create revision, returning `ErrSessionExpired` otherwise, as for a missing key.

Fixes #22613

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
