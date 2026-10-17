---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/etcd#22395 pr open: the same root cause in v3rpc.checkIntervals; its description names store.go:97 and :145 as "the same shape" and leaves them out
---

# grpcproxy: the range cache reads a from-key range end `"\x00"` as an empty interval

## Status

A bug (stale cached reads), outside the verified code: the gRPC proxy's range cache is not
translated. Found while verifying etcd#22395, which fixes the same reading of `"\x00"` in
`checkIntervals`.

## Where

`server/proxy/grpcproxy/cache/store.go` (fork `goose-lean`, 107edf7e4; the same at upstream
`main` d848b43ae): `cache.Add` builds a cached range's reverse-index interval as
`adt.NewStringAffineInterval(Key, RangeEnd)` (line 97) and `cache.Invalidate` builds a written
range's the same way (line 145). A `RangeEnd` of `"\x00"` (`clientv3.WithFromKey`, `WithPrefix`
of an all-`0xff` or empty key) means "every key from `Key` on" (the server's `mkGteRange`,
`watch.go:325`, `auth/range_perm_cache.go:43`), but in the affine order `[Key, "\x00")` is
empty; the open end is `""`. The proxy's `kvProxy` (`server/proxy/grpcproxy/kv.go`) serves
serializable ranges from the cache (line 49), adds every range response to it (lines 72, 109)
and invalidates it on each put, delete and txn it forwards (lines 83, 91, 102, 105, 124).

## What happens

- A cached serializable from-key range `[a, +inf)` is not invalidated by a put of `b` through the
  proxy: the next serializable `Get("a", WithFromKey(), WithSerializable())` through the proxy
  returns the old response, without `b`.
- A from-key delete `DeleteRange("a", WithFromKey())` through the proxy invalidates only the cached
  ranges containing the point `a`: a cached `[b, z)` is still served, with the deleted keys.

Reproduction (`notes/pr-verify/etcd-22395/server/proxy/grpcproxy/cache/store_fromkey_test.go` on
branch `pr-verify/etcd-22395`; a Go test in package `cache` next to `store.go`, importing
`pb "go.etcd.io/etcd/api/v3/etcdserverpb"`; both subtests fail at the PR head eb347e2b4, whose
`store.go` is upstream `main` d848b43ae's):

```go
func TestCacheFromKeyInvalidate(t *testing.T) {
	t.Run("cached from-key range, put of a key in it", func(t *testing.T) {
		c := NewCache(DefaultMaxEntries)
		req := &pb.RangeRequest{Key: []byte("a"), RangeEnd: []byte{0}}
		c.Add(req, &pb.RangeResponse{})
		c.Invalidate([]byte("b"), nil) // what the proxy's Put("b") does
		if _, err := c.Get(req); err == nil {
			t.Errorf("cached range [a, +inf) still served after a put of b")
		}
	})
	t.Run("cached range, from-key delete over it", func(t *testing.T) {
		c := NewCache(DefaultMaxEntries)
		req := &pb.RangeRequest{Key: []byte("b"), RangeEnd: []byte("z")}
		c.Add(req, &pb.RangeResponse{})
		c.Invalidate([]byte("a"), []byte{0}) // what the proxy's DeleteRange("a", WithFromKey()) does
		if _, err := c.Get(req); err == nil {
			t.Errorf("cached range [b, z) still served after a delete of [a, +inf)")
		}
	})
}
```

```
--- FAIL: TestCacheFromKeyInvalidate/cached_from-key_range,_put_of_a_key_in_it
    store_fromkey_test.go:18: cached range [a, +inf) still served after a put of b
--- FAIL: TestCacheFromKeyInvalidate/cached_range,_from-key_delete_over_it
    store_fromkey_test.go:27: cached range [b, z) still served after a delete of [a, +inf)
```

## Expected

The cache invalidates every cached range a forwarded write overlaps, as it does for a bounded
range: a client of the proxy reads its own writes in serializable ranges. (Serializable reads may be
stale with respect to other clients' writes; the invalidation exists for the proxy's own.)

## How the proof handles it

Out of scope: `server/proxy/grpcproxy` is not translated.

## Possible fixes

Normalise `"\x00"` to `""` before building the interval in `Add` and `Invalidate`, as
etcd#22395 does in `checkIntervals` and `auth/range_perm_cache.go:43-48` does.

## Found

2026-10-16, by the reviewer of the etcd#22395 verification (`notes/pr-verify/etcd-22395.md`).
