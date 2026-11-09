/-
`clientv3.New` (`client/v3/client.go`).

Users: every client program: `examples/lib/etcdstart` (`NewClient`), `examples/etcd/auth`
(`newUserClient`: a user name and password), `client/v3/kubernetes.New` (Kubernetes' storage factory:
TLS, dial options with chained interceptors, a stats handler and a context dialer, a logger),
`examples/k8s/*`; snippets `clientv3client/lifecycle.go` (`ReqNewWrapClose`, `ReqNewNoEndpoints`),
`clientv3client/auth.go` (`ReqUserClient`).

Proof sketch: no endpoint: `ErrNoAvailableEndpoints`. Else `newClient(&cfg)` (its spec) with the
configuration's copy.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/New.lean` (plain endpoints, no TLS, no token,
no dial options, keepalive, auto-sync or version check, `clientCfgOk`; the result `isNewClient` with
its watch environment): any configuration `cfgOk` admits (TLS, a token or a user name, Kubernetes'
dial options, auto-sync with verification off, `RejectOldCluster`), the principal `who` the
configuration names, the result W0's `clientMut` (the `KV` field writable, Kubernetes wraps it).

Round 1: no endpoint: an error and `nil` (the post says so); the endpoints token (with auto-sync
off the caller owns the endpoint list, `epsTok`); the principal per call (W0's round 3: `who` is the
default one); `cfgPrincipal_user`'s certificate premise; `cfgOk`'s dial options may replace the
client's interceptor (the gRPC proxy).

Margin: a zap `LogConfig` without a `Logger` is out of scope (`cfgOk`); with both a token and a
user name (`ErrMutuallyExclusiveCfg`) `cfgPrincipal` has no introduction, so no caller can call
`New` so (the error is the only outcome).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `New(cfg)`: a client of `γ` as `who` with its `KV` field writable (`clientMut`), or an error
and `nil`. -/
def New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.client.v3.Config) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cfgOk cfg γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cfg))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜cfg.Endpoints'.len = W64 0 → c = null ∧ err ≠ GoInterface.nil⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ clientMut c γ who ∗
         (⌜cfg.AutoSyncInterval' ≠ W64 0⌝ ∨
          ∃ eps, cfg.Endpoints' ↦*□ eps ∗ epsTok c (DFrac.own 1) eps)) ∨
       ⌜c = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
