/-
`transport.TLSInfo.ClientConfig` (`client/pkg/v3/transport/listener.go`).

Users: Kubernetes' storage factory (`factory/etcd3.go:286-299`: the client's `TLS`, discarded when
no file is given), etcdctl; snippet `clientv3client/tls.go` (`ReqNewTLS`).

Proof sketch: `baseConfig` (reads the certificate and key files: `tls.LoadX509KeyPair`, trusted
`crypto/tls` and `os`), the CA pool, the server name: a fresh configuration the caller owns and may
share read-only (`tlsCfgOk`), or an error.

Changes: new (round 1: the completeness review's F5).

Margin: which certificate (hence which principal, `tlsPrincipal`) is not described.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Transport

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.transport.Assumptions]

/-- `info.ClientConfig()`: a TLS configuration the client may use, or an error. -/
def TLSInfo.ClientConfig.spec : Prop :=
  ∀ (info : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport }}
    (App (Val (info @!! go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo.ty @!! go!"ClientConfig")) (Val #()))
  {{ (cfg : Loc) (err : GoInterface), RET (PairV #cfg #err);
      (⌜err = GoInterface.nil⌝ ∗ tlsCfgOk cfg) ∨ ⌜cfg = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end Transport
end EtcdGrove
end Perennial
