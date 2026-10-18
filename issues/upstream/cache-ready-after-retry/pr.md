Title: cache: initialize the demux before registering the store watcher

[`Cache.watch`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/cache/cache.go#L348-L370) registers its store watcher with the demux, and [`watchEvents`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/cache/cache.go#L405-L408) calls `demux.Init` and `ready.Set` under a `sync.Once` on the first response of the upstream watch. On a retry, [`demux.Init`](https://github.com/etcd-io/etcd/blob/b25719d10cdc41fb707b0d9f819c2529dec5d590/cache/demux.go#L119-L143) purges the demux unless the watch starts right after the demux's last revision, stopping the store watcher just registered; `watch` then loops with the `sync.Once` used, so `ready.Set` never runs again. This PR calls `demux.Init` when `watch` is entered, before the store watcher is registered.

Fixes #<issue>

`TestCacheReadyAfterWatchRetry` runs the issue's example; it fails on `main` and passes with this change.

Written with the assistance of generative AI; I reviewed and tested every change.
