/-
`credentials.NewTransportCredential` (`client/v3/credentials/credentials.go`).

Users: `newClient` (`cfg.TLS`), `Client.credentialsForEndpoint` (`nil` for `https` without TLS).

Proof sketch: `grpccredentials.NewTLS(cfg)` (2a: clones the configuration, read-only).

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Credentials

open Iris Iris.BI EtcdModel ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `NewTransportCredential(cfg)`: transport credentials. -/
def NewTransportCredential.spec : Prop :=
  ∀ (cfg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials ∗ (⌜cfg = null⌝ ∨ Transport.tlsCfgOk cfg) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewTransportCredential)) (Val #cfg))
  {{ (creds : GoInterface), RET #creds; transportCredsOk creds }}

end spec

end Credentials
end EtcdGrove
end Perennial
