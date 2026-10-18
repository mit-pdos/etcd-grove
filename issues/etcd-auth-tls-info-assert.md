---
upstream: none
checked: 2026-10-18
links:
---

# auth: `AuthInfoFromTLS` panics for a peer whose credentials are not TLS (undocumented)

- **Status**: **fixed in the fork** (D19l, 2026-10-18): the two-result assertion below, with the
  reproduction as a test (`TestAuthInfoFromTLSNonTLSPeer`, panics without the fix), on
  `upamanyus/etcd` `goose-lean` as `17c88a667` (etc/goose.py's etcd pin since then; upstream main
  unchanged). At upstream's code: documentation (an unstated precondition; unreachable in etcd's server, whose
  gRPC servers have TLS transport credentials or none: grpc then leaves `peer.AuthInfo` nil, and
  its HTTP handler transport sets a `credentials.TLSInfo` only for a TLS request).
- **Where**: `server/auth/store.go` at the pinned revision (`etc/goose.py`, bc8b52a50319):
  `authStore.AuthInfoFromTLS` (`store.go:1013-1054`) asserts `peer.AuthInfo.(credentials.TLSInfo)`
  (`store.go:1019`) with the one-result form, which panics for any other `credentials.AuthInfo`
  (ALTS, local, insecure credentials). The `AuthStore` interface (`AuthInfoFromTLS gets AuthInfo
  from TLS info of gRPC's context`) does not say it requires TLS credentials.
- **What happens**: a context whose peer has `insecure.NewCredentials()`'s auth info panics
  (`interface conversion: credentials.AuthInfo is insecure.info, not credentials.TLSInfo`).
  Reproduction (in `server/auth`):

  ```go
  func TestAuthInfoFromTLSNonTLSPeer(t *testing.T) {
  	as := &authStore{lg: zaptest.NewLogger(t)}
  	_, ai, _ := insecure.NewCredentials().ServerHandshake(nil)
  	ctx := peer.NewContext(context.Background(), &peer.Peer{AuthInfo: ai})
  	as.AuthInfoFromTLS(ctx) // panics
  }
  ```
- **How it happens**: the function returns `nil` for a peer with no auth info, but asserts any
  other auth info to `credentials.TLSInfo` without the `ok` form.

  1. A gRPC server built with non-TLS transport credentials (here `insecure.NewCredentials()`)
     puts that credentials' `AuthInfo` in the request's peer.
  2. The caller passes the request's context to `AuthInfoFromTLS`. The peer's `AuthInfo` is
     non-nil, so the early return is skipped.
  3. The assertion to `credentials.TLSInfo` fails and panics.

  ```go
  // server/auth/store.go:1013-1020 (etcd main f061acd09)
  func (as *authStore) AuthInfoFromTLS(ctx context.Context) (ai *AuthInfo) {
  	peer, ok := peer.FromContext(ctx)
  	if !ok || peer == nil || peer.AuthInfo == nil {
  		return nil
  	}

  	tlsInfo := peer.AuthInfo.(credentials.TLSInfo) // <- panics for non-TLS auth info
  	for _, chains := range tlsInfo.State.VerifiedChains {
  ```
- **Expected**: `nil` (no TLS identity), as for a peer without auth info.
- **How the proof handles it**: `AuthInfoFromTLS` is at the trust boundary (its peer's
  `credentials.TLSInfo` and x509 chains are axiomatized types); its axiom
  (`Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromTLS.lean`) takes any context. Until
  D19l it did not state the panic (false of upstream's code for a non-TLS peer); since the fork's
  fix it is true as stated (a non-TLS peer gets `nil`).
- **Possible fixes**: `tlsInfo, ok := peer.AuthInfo.(credentials.TLSInfo); if !ok { return nil }`.
- **Found**: 2026-10-14, the auth store's request side (unit P2).
