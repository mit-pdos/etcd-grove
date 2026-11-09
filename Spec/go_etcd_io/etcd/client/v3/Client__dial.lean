/-
`(*clientv3.Client).dial` (`client/v3/client.go`).

Users: `dialWithBalancer`, `Dial`.

Proof sketch: `dialSetupOpts` (its spec); the token bundle's per-RPC credentials if any
(`bundleAt _ γ who`: every token names `who`); `cfg.DialOptions` (`dialOptsOk`); the target string
(`fmt.Sprintf`, `authority`); `grpc.NewClient(target, opts...)` (2a: a connection whose unary calls
go through `uiOk`'s interceptor over invokers meeting `AttemptTriple` for `γ` and `who`, its streams
through `siOk`'s: `connOk`), or an error.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__dial.lean`: the result `connOk`.

Margin: none.
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

/-- `c.dial(creds, dopts...)`: a connection to the cluster as `who`, or an error. -/
def Client.dial.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (creds : GoInterface) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ transportCredsOk creds ∗ dialTargetOk sl γ }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dial")) (Val #creds)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ connOk conn γ who) ∨ ⌜conn = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
