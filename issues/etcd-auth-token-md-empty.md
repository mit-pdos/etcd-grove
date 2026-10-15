# auth: `AuthInfoFromCtx` panics on a token key with no value in the incoming metadata

- **Status**: open, robustness (a reachable panic only through an in-process caller: grpc's
  transports never put a key with no value in a request's metadata).
- **Where**: `server/auth/store.go` at the pinned revision (`etc/goose.py`, bc8b52a50319):
  `authStore.AuthInfoFromCtx` (`store.go:1056-1084`) looks up `md["token"]` (then
  `md["authorization"]`) and indexes `ts[0]` (`store.go:1075`) without checking that the list is
  non-empty. `metadata.MD` is a `map[string][]string`, and `metadata.NewIncomingContext` accepts
  any map; the `AuthStore` interface (`AuthInfoFromCtx gets AuthInfo from gRPC's context`) states
  no precondition.
- **What happens**: `as.AuthInfoFromCtx(metadata.NewIncomingContext(ctx, metadata.MD{"token": {}}))`
  on an auth-enabled store panics with `index out of range [0] with length 0`. Reproduction (in
  `server/auth`):

  ```go
  func TestAuthInfoFromCtxEmptyTokenValues(t *testing.T) {
  	tp, _ := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
  	as := &authStore{lg: zaptest.NewLogger(t), enabled: true, tokenProvider: tp}
  	ctx := metadata.NewIncomingContext(context.Background(), metadata.MD{"token": {}})
  	as.AuthInfoFromCtx(ctx) // panics
  }
  ```
- **How it happens**: the lookup checks that the key is present, not that its value list is
  non-empty.

  1. Auth is enabled. An in-process caller builds a context with
     `metadata.NewIncomingContext(ctx, metadata.MD{"token": {}})`.
  2. `AuthInfoFromCtx` finds the `token` key, so `ok` is true and `ts` is the empty list.
  3. `ts[0]` panics with an index out of range.

  ```go
  // server/auth/store.go:1061-1075 (etcd main f061acd09)
  	md, ok := metadata.FromIncomingContext(ctx)
  	if !ok {
  		return nil, nil
  	}

  	// TODO(mitake|hexfusion) review unifying key names
  	ts, ok := md[rpctypes.TokenFieldNameGRPC]
  	if !ok {
  		ts, ok = md[rpctypes.TokenFieldNameSwagger]
  	}
  	if !ok {
  		return nil, nil
  	}

  	token := strings.TrimPrefix(ts[0], "Bearer ") // <- ts may be empty
  ```
- **Expected**: no token (`nil, nil`), or `ErrInvalidAuthToken`.
- **How the proof handles it**: the axiom of `metadata.FromIncomingContext`
  (`Spec/google_golang_org/grpc/metadata/FromIncomingContext.lean`) states that every value list
  of the returned metadata is non-empty: true of grpc's transports, narrower than grpc's code.
- **Possible fixes**: `if !ok || len(ts) == 0 { return nil, nil }` (and the same for the
  `authorization` key).
- **Found**: 2026-10-14, the auth store's request side (unit P2), proving `AuthInfoFromCtx`.
