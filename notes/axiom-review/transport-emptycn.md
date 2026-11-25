# Review: `transport.NewTimeoutTransport` and certificates (2026-11-25)

**Target.** `axiom transport.NewTimeoutTransport.wp_proof`
(`Proof/go_etcd_io/etcd/client/pkg/v3/transport/NewTimeoutTransport.lean`, spec
`Spec/go_etcd_io/etcd/client/pkg/v3/transport/NewTimeoutTransport.lean`), as on `lean` at `4efaa9ffc8`: an error or
a round tripper for **every** `TLSInfo`. It is the trust boundary under `rafthttp.NewRoundTripper` and
`newStreamRoundTripper` (proved over it), so under `bootstrap`'s round tripper (`bootstrap.go:72`,
`cfg.PeerTLSInfo`) and `Transport.Start`'s (`NewServer`'s transport, `TLSInfo: cfg.PeerTLSInfo`).

**Finding (refuted), by an independent axiom review.** `NewTimeoutTransport` → `NewTransport` →
`info.ClientConfig()` (`client/pkg/transport/listener.go:559-614` at the etcd pin). With `EmptyCN` set and a
certificate, `ClientConfig` loads the certificate in `baseConfig` (`:376`), then reads the file again through
`tlsutil.NewCert` with a parse function that does `block, _ = pem.Decode(certPEMBlock);
x509.ParseCertificate(block.Bytes)` (`:588-594`). If the file has no PEM block at the second read, `block` is nil
and the dereference panics. A program that rewrites the certificate file while calling `NewTimeoutTransport` panics;
the axiom said it does not.

- **Go (the review's):** `TestEmptyCN` (a FIFO serving a valid certificate, then junk) and `TestEmptyCNRace` (a
  goroutine renaming junk and the certificate over the file in turn), 5/5 runs each, against the pinned
  `client/pkg`.
- **Go (the upstream report):** `issues/etcd-transport-emptycn-cert-reread-panic/` (`ClientConfig` with `EmptyCN`,
  as `etcd grpc-proxy --cert --key` builds it, while the same valid certificate is rewritten in place:
  truncate, write), 5/5 runs at `client/pkg/v3@v3.7.4`, go1.27.3.
- **A second route, found while fixing (code reading, then a probe):** with a certificate and `AllowedCN` set,
  `baseConfig` calls `info.Logger.Warn` (`:426`), which panics on a non-nil zero `&zap.Logger{}` (its core is a
  nil interface). A probe test (`TLSInfo{CertFile, KeyFile, AllowedCN: "x", Logger: &zap.Logger{}}`) panicked
  1/1. Not an etcd bug (a zero zap logger is not a logger), but the axiom covered it.
- **Reach.** `bootstrap.wp_proofOne` (the interim axiom of `dist-putget-interim`) inherits the gap through
  `cfg.PeerTLSInfo`. On `lean` the proved `bootstrap.wp_proof` and `NewServer`/`NewServerR` applied the round
  trippers' specs at `cfg.PeerTLSInfo`, with nothing about it in their premises; every example's configuration
  leaves `PeerTLSInfo` zero, so no closed theorem was vacuous on this account, but the contracts claimed more
  than Go does.

**Fix (2026-11-25, branch `transport-emptycn/2026-11-25`).** The spec covers only a `TLSInfo` with no certificate
and no key file, `transport.tlsEmpty info` (Go's `info.Empty()`; `Proof/go_etcd_io/etcd/client/pkg/v3/transport/Defs.lean`),
a premise. Of the two options the task named, `EmptyCN = false ∨ Empty()` and "the panic allowed": the second has
no form in a WP (a panic is excluded, not an outcome), and the first still covers `baseConfig`, whose
logger route above refutes it too. `Empty()` keeps the axiom to the path that loads no certificate (a server name,
a CA pool from `TrustedCAFile` whose decode loop checks the block, and with `EmptyCN` the error of reading `""`),
which is less trusted text and is what every caller has. Restated with it: `rafthttp.NewRoundTripper.spec`,
`newStreamRoundTripper.spec` (a premise on `tls`), `rafthttp.Transport.Start.spec` (a conjunct
`transport.tlsEmpty tv.TLSInfo'` of its pure precondition) and `bootCfgOk` (a conjunct `transport.tlsEmpty
cfg.PeerTLSInfo'`), which `bootstrap.spec`, `NewServer.spec`, `NewServerR.spec` and `bootstrapContract` take
already; `etcdstart.bootCfgOk_of` discharges it from the configuration literal (`PeerTLSInfo` zero). No axiom
added; `bootstrapContract`'s docstring no longer lists `PeerTLSInfo` among the fields that "make it return an
error or do what `bootOk` says".

**Margin.** Peer TLS with certificates is now outside every contract. Covering it would need the certificate
path's own spec: `EmptyCN` off (or the upstream fix), `info.Logger` nil or a zap logger, and the handshake
callbacks (`GetClientCertificate` re-reads and logs on every handshake).
