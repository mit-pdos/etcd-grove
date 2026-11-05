# `auth.NewAuthStore`'s `Close` conjunct (`authCloseOk`)

**Reviewed (2026-11-05, R2b-3d stage 5b, branch `r2b3`):** the conjunct `authCloseOk stl` that the
user approved for `auth.NewAuthStore.wp_proof`'s post (`Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`),
with its definition (`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`):

```lean
def authCloser (ast : Loc) (K : IProp GF) : IProp GF :=
  iprop(□ {{ isPkgInit auth ∗ K }} ast.Close() {{ (err : GoInterface), RET #err; ⌜err = nil⌝ ∗ K }})
def authCloseOk (ast : Loc) : IProp GF := authCloser ast iprop(True)
```

Go: etcd at the pin (`upamanyus/etcd` `673da07c8`), `server/auth/store.go:327-335`.

**Verdict: survives.**

## The claim

The store `NewAuthStore` returns can be closed any number of times, by anyone holding nothing,
and each `Close` returns `nil` without panicking.

## The Go code

```go
func (as *authStore) Close() error {
	as.enabledMu.Lock()
	defer as.enabledMu.Unlock()
	if !as.enabled {
		return nil
	}
	as.tokenProvider.disable()
	return nil
}
```

## Attacks tried

1. **A panic in `Close`.** `enabledMu` is a `sync.RWMutex` field of the store `NewAuthStore`
   allocates, so it is not nil. `Lock` cannot panic: an unlock of an unlocked mutex needs an
   `Unlock` without a `Lock`, and every method pairs them under `defer`. A `Lock` held for good is
   a deadlock, which a WP (partial correctness) does not exclude.
2. **`enabled` true, so `disable()` runs.** The axiom's other contracts are for auth off: only
   `AuthEnable` sets `enabled`, and the off contract (`isAuthStore … false`) never lends it. Even
   enabled, the server's providers' `disable` (`tokenSimple.disable`: stops the TTL keeper under
   its own lock, idempotent; `tokenNop.disable`: nothing; `tokenJWT.disable`: nothing) does not panic,
   twice included.
3. **`Close` repeated, or concurrent with reads and `Recover`.** `Close` reads `enabled` only and
   writes nothing, so neither later methods nor later `Close`s see a difference. `Recover` writes
   `enabled = false` under the same lock. Go test below: three sequential `Close`s, sixteen
   concurrent ones racing `IsAuthEnabled`/`Revision`, then `Recover` on another backend and
   `Close` again, all `nil`, with no race reports.
4. **Inconsistency with the axiom's other conjuncts.** `authCloser` is persistent and its pre and
   post are the same resource (`True`), so it grants nothing that could be duplicated or held
   twice.

Not tried: a `Close` racing `AuthEnable` (an admin request the off contract never admits).

## The Go test

`server/storage/schema/zz_close_axiom_test.go`, at the pin, run with `GOTOOLCHAIN=go1.27.3 go
test -race -count=3 -run TestBksCloseAfterNew ./storage/schema/` (not committed: it is in the
`schema` package because it builds a real `schema.NewAuthBackend`):

```go
package schema

import (
	"sync"
	"testing"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"

	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// The axiom review of auth.NewAuthStore's Close conjunct (etcd-grove, 2026-11-05): after
// NewAuthStore over a fresh backend with the simple token provider (the server's), the
// store's Close returns nil, any number of times, concurrently with the store's reads,
// and after a Recover on another fresh backend.
func TestBksCloseAfterNew(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be)
	tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} { c := make(chan struct{}); close(c); return c }, 300_000_000_000)
	if err != nil {
		t.Fatal(err)
	}
	as := auth.NewAuthStore(lg, NewAuthBackend(lg, be), tp, bcrypt.MinCost)
	for i := 0; i < 3; i++ {
		if err := as.Close(); err != nil {
			t.Fatalf("Close %d: %v", i, err)
		}
	}
	var wg sync.WaitGroup
	for i := 0; i < 16; i++ {
		wg.Add(2)
		go func() {
			defer wg.Done()
			if err := as.Close(); err != nil {
				panic(err)
			}
		}()
		go func() {
			defer wg.Done()
			_ = as.IsAuthEnabled()
			_ = as.Revision()
		}()
	}
	wg.Wait()
	be2, _ := betesting.NewDefaultTmpBackend(t)
	defer betesting.Close(t, be2)
	as.Recover(NewAuthBackend(lg, be2))
	if err := as.Close(); err != nil {
		t.Fatalf("Close after Recover: %v", err)
	}
	if as.IsAuthEnabled() {
		t.Fatal("enabled")
	}
}
```

Output:

```
=== RUN   TestBksCloseAfterNew
--- PASS: TestBksCloseAfterNew (0.03s)
=== RUN   TestBksCloseAfterNew
--- PASS: TestBksCloseAfterNew (0.02s)
=== RUN   TestBksCloseAfterNew
--- PASS: TestBksCloseAfterNew (0.02s)
PASS
ok  	go.etcd.io/etcd/server/v3/storage/schema	1.103s
```
