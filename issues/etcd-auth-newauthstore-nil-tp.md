---
upstream: none
checked: 2026-10-20
links: []
---

# server/auth: `NewAuthStore` needs a non-nil token provider when the backend has auth enabled

- **Status**: a precondition the code needs that its API does not state. Not reachable through
  `NewServer`, which passes `NewTokenProvider`'s result (never nil on success); tests pass `nil`
  (`server/etcdserver/server_test.go:806`, `server/etcdserver/api/etcdhttp/health_test.go:164`) and
  work only because their backends are fresh.
- **Where**: the fork `upamanyus/etcd` at `107edf7e4` (`etc/goose.py`'s etcd pin).
  `NewAuthStore(lg, be, tp, bcryptCost)` (`server/auth/store.go:944-992`) reads the backend's
  auth-enabled flag (line 965) and, if it is set, calls `as.tokenProvider.enable()` (line 977).
- **What happens**: with a nil `tp` and a backend where auth was enabled, a nil-pointer panic.
  Reproduction (a test in `server/auth`, `go test -run TestNewAuthStoreNilTokenProviderAuthEnabled
  .`; it passes, i.e. confirms the panic, at the pin):

  ```go
  func TestNewAuthStoreNilTokenProviderAuthEnabled(t *testing.T) {
  	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
  	if err != nil {
  		t.Fatal(err)
  	}
  	be := newBackendMock()
  	as := NewAuthStore(zaptest.NewLogger(t), be, tp, bcrypt.MinCost)
  	if err := enableAuthAndCreateRoot(as); err != nil {
  		t.Fatal(err)
  	}
  	as.Close()
  	defer func() {
  		r := recover()
  		if r == nil {
  			t.Fatal("expected a panic")
  		}
  		t.Logf("NewAuthStore(nil tp) on an auth-enabled backend panicked: %v", r)
  	}()
  	NewAuthStore(zaptest.NewLogger(t), be, nil, bcrypt.MinCost)
  }
  ```
- **Expected**: the API documents that `tp` must not be nil (or `NewAuthStore` tolerates it,
  e.g. by using a no-op provider).
- **How the proof handles it**: `auth.NewAuthStore`'s contract is pending (`?` in
  `etc/link-lean-first-server.txt`); its true statement takes the token provider's contract
  (`auth.tokenProviderOk tp`, which implies `tp ≠ nil`) as a premise (`notes/STATUS.md`, "Server
  construction, unit N1").
- **Possible fixes**: document the precondition on `NewAuthStore`, or substitute
  `newTokenProviderNop()` for a nil `tp`.
- **Found**: 2026-10-17, auditing the contract of `auth.NewAuthStore` for `NewServer`'s proof
  (unit N1 of the server-construction unit).
