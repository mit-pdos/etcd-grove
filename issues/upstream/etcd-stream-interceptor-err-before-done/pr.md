Title: etcdserver: do not report a stream's cancel reason before it is done

[`cancellableContext.Cancel`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/interceptor.go#L286-L293) stores the reason under its lock, releases the lock, and only then closes `Done()`, while [`Err`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/api/v3rpc/interceptor.go#L295-L304) returns the stored reason without looking at `Done()`. In between, `Err` is non-nil on a context that is not done, which `context.Context` forbids. This PR closes `Done()` before releasing the lock, as Go's own `cancelCtx` does.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
