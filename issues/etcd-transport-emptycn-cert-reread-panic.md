---
upstream: none
checked: 2026-11-25
links:
  - etcd-io/etcd#10343 pr merged: added the EmptyCN check this bug is in (related, not this bug)
blocks-proof: no
---

# client/pkg/transport: ClientConfig with EmptyCN panics if the certificate file is rewritten while it loads

`TLSInfo.ClientConfig` (and `NewTransport`/`NewTimeoutTransport`, which call it) panics with a
nil pointer dereference when `EmptyCN` is set and the certificate file is replaced in place while
it runs, e.g. by `cp renewed.pem cert.pem` (truncate, then write). `etcd grpc-proxy --cert --key`
builds its client TLS configuration this way.

**Expected:** ClientConfig should return a configuration or an error, as for every other unreadable
or malformed certificate file ("ClientConfig() will return an error for a cert with non empty CN",
[`EmptyCN`'s doc](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/client/pkg/transport/listener.go#L204-L206)).

**Impact:** a gRPC proxy started (or a program building a client transport with `EmptyCN`) while
its client certificate is being rotated by a non-atomic write crashes instead of failing with an
error. The window is the time between two reads of the file inside one call, so it takes a
rotation at startup; etcd's server does not set `EmptyCN`. Every release since v3.4 (#10343).

**Reproduction:** `TestClientConfigEmptyCNCertRewritten` in
[`issues/etcd-transport-emptycn-cert-reread-panic/emptycn_reread_test.go`](etcd-transport-emptycn-cert-reread-panic/emptycn_reread_test.go),
copied into `client/pkg/transport` at etcd-io/etcd v3.7.4 (`go.etcd.io/etcd/client/pkg/v3@v3.7.4`;
`main` at `4e090c033` has the same code, checked 2026-11-25), go1.27.3 (5 runs of 5 fail):

```
$ go test ./transport -run TestClientConfigEmptyCNCertRewritten -count=1
--- FAIL: TestClientConfigEmptyCNCertRewritten (0.00s)
    emptycn_reread_test.go:78: ClientConfig panicked while the certificate file was rewritten: runtime error: invalid memory address or nil pointer dereference
```

**Cause:** `ClientConfig` loads the certificate in `baseConfig`
([listener.go#L376](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/client/pkg/transport/listener.go#L376)),
then, for `EmptyCN`, reads the file again through `tlsutil.NewCert` with a parse function that
does `block, _ = pem.Decode(certPEMBlock); x509.ParseCertificate(block.Bytes)`
([listener.go#L588-L594](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/client/pkg/transport/listener.go#L588-L594)).
The first load succeeding does not make the second read contain a PEM block: if the file is empty
or truncated by then, `pem.Decode` returns a nil block and `block.Bytes` dereferences it.

## Proof

no: `transport.NewTimeoutTransport`'s trust-boundary spec now covers only a `TLSInfo` with no
certificate and key files (`transport.tlsEmpty`, `Spec/go_etcd_io/etcd/client/pkg/v3/transport/NewTimeoutTransport.lean`),
which every configuration of the proofs meets (`PeerTLSInfo` zero; only grpc-proxy sets `EmptyCN`).
Until 2026-11-25 the spec promised no panic for every `TLSInfo` (found by an independent axiom review,
`notes/axiom-review/transport-emptycn.md`).

## Fix

Check the decoded block: `if block == nil { return tls.Certificate{}, errors.New("...: no PEM data") }`
before `x509.ParseCertificate`; or check the CN of the certificate `baseConfig` already loaded
instead of reading the file a second time.
