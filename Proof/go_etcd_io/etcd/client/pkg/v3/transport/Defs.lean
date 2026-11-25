/-
The vocabulary of `transport`'s specs (`go.etcd.io/etcd/client/pkg/v3/transport`, names-only).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.client.pkg.v3

section defs
variable [GooseExts]

/-- **`info.Empty()`**: no certificate and no key file (`client/pkg/transport/listener.go:216-218`,
`info.CertFile == "" && info.KeyFile == ""`; `""` as the zero `GoString`), the TLS configuration of a plain-HTTP peer.
(2026-11-25, `notes/axiom-review/transport-emptycn.md`) The client configuration of such an `info`
(`ClientConfig`) loads no certificate: a `tls.Config` with its server name, its CA pool if
`TrustedCAFile` is set, and, with `EmptyCN`, the error of reading the file `""`. With a certificate it
calls `baseConfig`, which reads the files, logs through `info.Logger`, and installs the handshake
callbacks, and `EmptyCN` re-reads the certificate and dereferences `pem.Decode`'s block unchecked
(`issues/etcd-transport-emptycn-cert-reread-panic.md`): a trust-boundary spec covering that path
would have to state what each of these needs. -/
def transport.tlsEmpty (info : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo) : Prop :=
  info.CertFile' = (zeroValDef : GoString) ∧ info.KeyFile' = (zeroValDef : GoString)

end defs

end EtcdGrove
end Perennial
