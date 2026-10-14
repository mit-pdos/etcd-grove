# auth: `AuthInfoFromTLS` panics for a peer whose credentials are not TLS (undocumented)

- **Status**: open, documentation (an unstated precondition; unreachable in etcd's server, whose
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
- **Expected**: `nil` (no TLS identity), as for a peer without auth info.
- **How the proof handles it**: `AuthInfoFromTLS` is at the trust boundary (its peer's
  `credentials.TLSInfo` and x509 chains are axiomatized types); its axiom
  (`Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromTLS.lean`) does not state the
  panic, which etcd's server configuration rules out.
- **Possible fixes**: `tlsInfo, ok := peer.AuthInfo.(credentials.TLSInfo); if !ok { return nil }`.
- **Found**: 2026-10-14, the auth store's request side (unit P2).
