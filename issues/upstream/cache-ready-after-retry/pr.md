Title: cache: initialize the demux before registering the store watcher

[`Cache.watch`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/cache/cache.go#L348-L370) registers its store watcher with the demux, then calls `demux.Init` and sets the cache ready on the upstream watch's first response, once per call ([`watchEvents`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/cache/cache.go#L405-L408)). On a resync, [`demux.Init`](https://github.com/etcd-io/etcd/blob/22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4/cache/demux.go#L119-L143) purges the demux unless the watch continues from its last revision, assuming that only the previous watch's watchers are registered; the purge also stops the new store watcher, and `watch` reopens the upstream watch but never sets the cache ready again. This PR calls `demux.Init` before the store watcher is registered.

Fixes #22614

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
