---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22065 issue open: this bug (reported on v3.6.12 and v3.6.13)
  - etcd-io/etcd#22112 pr closed: keyed the cache on the caller's token and flushed it on auth changes; closed unmerged (2026-10-13)
  - etcd-io/etcd#22397 issue open: related, different (the same cache treats an open-ended range end as its start key, so cached serializable reads go stale)
---

# grpcproxy: the serializable Range cache answers any caller, before auth

- **Status**: a bug (an authorization bypass when auth is enabled on the backend: the gRPC proxy
  returns a cached `Range` response to a caller the backend would deny). Security-relevant;
  public upstream (etcd-io/etcd#22065). Not in translated code: `server/proxy/grpcproxy` has no
  `Code/` module.
- **Where** (etcd pin `107edf7e4`, `server/proxy/grpcproxy/`):
  - `kv.go:47-76` (`kvProxy.Range`: a serializable request is answered from `p.cache.Get(r)`
    before anything is forwarded; every forwarded response, linearizable ones too, is stored
    with `Serializable = true`);
  - `kv.go:98-112` (`txnToCache`: the range responses of a `Txn` are stored the same way);
  - `cache/store.go:46-53` (`keyFunc`: the key is the marshaled `RangeRequest` alone, with no
    token, user or auth revision), `:77` (`Add`), `:116-131` (`Get`).
- **What happens**: once an authorized caller's range (directly, or inside a `Txn`) has filled
  the cache, a serializable `Range` with the same request bytes from another caller (one with no
  permission on the range, or with no credentials) gets the cached response. The backend's
  authorization never runs for it. Permission changes do not touch the cache either.
  Reproduction at the pin, with a fake backend `KV` that denies a caller without a token:
  `issues/etcd-grpcproxy-range-cache-auth/range_cache_auth_test.go` (dropped into
  `server/proxy/grpcproxy/`; `go test ./proxy/grpcproxy/ -run TestRangeCacheIgnoresCaller -v`
  from `server/`). It passes at the pin: the caller without a token gets the value from the
  cache and the backend is not called. The end-to-end reproduction (a real backend with auth and
  `etcd grpc-proxy`) is the reporter's.
- **Expected**: a response produced for one identity is not served to another; a serializable
  `Range` through the proxy is denied when the backend would deny it.
- **How the proof handles it**: out of scope. `kvProxy` and its cache are not translated (no
  `Code/` module, no function in the verified-code inventory). On a cache hit no verified function
  runs. On a miss the request goes through the verified client and the server's `kvServer.Range`
  and `authApplierV3.Range`, whose specs are about the request that reached the server under its
  own context and cannot speak for a response the proxy hands to another caller. The auth specs
  also carry no caller identity yet (some auth info, or some error), so the property is not
  statable at present. Triage: `notes/bug-triage/etcd-22065.md` (proposal
  `grpcproxy-cache-auth`, on top of `inproc-client-auth-identity` and `auth-state-model`). The
  verified etcd `cache` package (`cache/v3`) likewise serves reads without an identity, by
  design: it has no auth surface.
- **Possible fixes** (the options in #22065): include the caller's identity and the auth revision
  in the cache key, and flush on auth changes (#22112's approach); revalidate the caller's
  permission with the backend before returning a cached response; or disable the Range cache
  when the backend has auth enabled.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22065.
