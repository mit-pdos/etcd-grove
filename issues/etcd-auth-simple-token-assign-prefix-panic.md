---
upstream: unchecked
checked: 2026-10-24
links:
---

# auth: the simple token provider's `assign` panics on a context with the index but no token prefix

- **Status**: an unstated precondition (a reachable panic only through an in-process caller of the
  exported `AuthStore.Authenticate`; etcd's own two callers always set both context values).
- **Where**: `server/auth/simple_token.go` at the pinned revision (`etc/goose.py`,
  bc8b52a50319): `tokenSimple.assign` (`simple_token.go:216-227`) reads the raft index with a
  checked type assertion, `ctx.Value(AuthenticateParamIndex{}).(uint64)` (returning
  `errors.New("failed to assign")` when it is absent), then the token's prefix with an unchecked
  one, `ctx.Value(AuthenticateParamSimpleTokenPrefix{}).(string)` (`simple_token.go:222`), which
  panics when the value is absent. `authStore.Authenticate` (`store.go:337`) passes its context
  to `assign` unchanged; the `AuthStore` interface (`store.go:101-102`: "Authenticate does
  authentication based on given user name and password") states nothing about the context's
  values. etcd's callers set both: the apply layer (`apply/backend.go:158`, the raft index and
  the request's `SimpleToken`) and `WithRoot` (`store.go:1184-1193`).
- **What happens**: with the simple provider and auth enabled, `as.Authenticate(ctx, "root", "")`
  on `ctx := context.WithValue(context.Background(), AuthenticateParamIndex{}, uint64(1))` panics
  with `interface conversion: interface {} is nil, not string`. Reproduction (in `server/auth`,
  not run here):

  ```go
  func TestAuthenticateNoSimpleTokenPrefix(t *testing.T) {
  	as, tearDown := setupAuthStore(t) // auth enabled, user "foo" with a password
  	defer tearDown(t)
  	ctx := context.WithValue(context.Background(), AuthenticateParamIndex{}, uint64(1))
  	as.Authenticate(ctx, "foo", "bar") // panics in tokenSimple.assign
  }
  ```
- **Expected**: an error, as for a missing index (`failed to assign`), or the precondition stated
  on `Authenticate`.
- **How the proof handles it**: not yet: the token provider is a contract
  (`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`, `tokenProviderOk`: `assign` on any
  context returns a token or an error), which no real provider is proved to meet; a proof of the
  simple provider's `assign` needs the two values as a premise of the contract (`notes/decisions.md`,
  "S5 of the auth plan").
- **Possible fixes**: `simpleTokenPrefix, ok := ctx.Value(AuthenticateParamSimpleTokenPrefix{}).(string);
  if !ok { return "", errors.New("failed to assign") }`.
- **Found**: 2026-10-24, the auth plan's S5, stating the token provider's contract for
  `Authenticate`.
