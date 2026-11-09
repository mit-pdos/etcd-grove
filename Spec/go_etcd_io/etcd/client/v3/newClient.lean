/-
`clientv3.newClient` (`client/v3/client.go`).

Users: `New`.

Proof sketch: transport credentials from `cfg.TLS` (`credentials.NewTransportCredential`, over
`tlsCfgOk`); `ErrMutuallyExclusiveCfg`; the client's context (`context.WithCancel` of `cfg.Context`
or `TODO()`: `ctxOk`, `ctxPrin _ who` by `ctxPrin_child`); the logger (`cfg.Logger`, or
`logutil.CreateDefaultZapLogger(ClientLogLevel())` named: `isLogger`); the credentials and the
token bundle (`credentials.NewPerRPCCredentialBundle`: `bundleAt _ γ who`, its token `""`); the call
options (`defaultCallOpts` or a literal of three: full slices, `callOptsOk _ false`; the size check's
error); the resolver (`resolver.New`), `SetEndpoints` (its spec: each endpoint `servesAt γ`):
`clientPre`. `dialWithBalancer` (its spec: `connOk` or an error, the resolver closed), `c.conn` set:
`clientConnOk`. The members: `NewCluster`, `NewKV` (W0), `NewLease`, `NewWatcher` (1b), `NewAuth`,
`NewMaintenance`, each over `clientCore`'s pieces; the `Auth` field set last of the ones the
interceptor reads (see the margin). `getToken` with the dial timeout (its spec; an error: `Close`,
returned). `checkVersion` if asked (an error: `Close`, returned). `go autoSync()` (its spec, over
`clientCore`). The fields but `KV` frozen (`clientMutRest`), `KV` writable: `clientMut`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/newClient.lean`: as `New`'s.

Margin: **the members are built before `c.Auth` is set**, and W0's `NewKV` (and the other
constructors) receive `clientConnOk` then: a call through it before `NewAuth` would, on a token
refusal, refresh the token through a `nil` `Auth` and panic. `newClient` makes no call before then,
but a persistent `clientConnOk` cannot say so: the realization needs a readiness witness (see
`notes/specs-only/batch-1c.md`, open question 1).
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

/-- `newClient(&cfg)`: as `New`, the configuration given back. -/
def newClient.spec : Prop :=
  ∀ (p : Loc) (cfg : go_etcd_io.etcd.client.v3.Config) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦ cfg ∗ cfgOk cfg γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.newClient)) (Val #p))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); p ↦ cfg ∗
      ((⌜err = GoInterface.nil⌝ ∗ clientMut c γ who) ∨ ⌜c = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
