/-
`(*clientv3.Client).dial` (`client/v3/client.go`).

Users: `dialWithBalancer`, `Dial`.

Proof sketch: `dialSetupOpts` (its spec); the target from `authority(c.endpoints[0])`, read without
`epMu` and without an emptiness check (`issues/etcd-client-dial-empty-endpoints.md`): the endpoints
token's fraction (no concurrent `SetEndpoints`) at a non-empty list; the token bundle's per-RPC credentials if any
(`bundleAt _ γ who`: every token names `who`; its credentials are grpc's `perRPCAt _ (Credentials.credMD
γ who)`, `rpcCredsAt_perRPC`, so the connection's `R` is `credMD γ who`, what 2a's `mdPrin_of` takes); `cfg.DialOptions` (`dialOptsOk`); the target string
(`fmt.Sprintf`, `authority`); `grpc.NewClient(target, opts...)` (2a's `Grpc.NewClient.spec`, its
workload premise `⌜Grpc.msgsFit⌝` from `clientPre` (`cfgOk`'s, kept by `newClient`): a connection whose unary calls
go through `uiOk`'s interceptor over invokers meeting `AttemptTriple` for `γ` and `who`, its streams
through `siOk`'s: `connOk`), or an error.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__dial.lean`: the result `connOk`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

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
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (creds : GoInterface) (sl : GoSlice) (dq : DFrac)
    (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ transportCredsOk creds ∗ dialTargetOk sl γ ∗ epsTok c dq eps ∗
      ⌜eps ≠ []⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dial")) (Val #creds)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err); epsTok c dq eps ∗
      ((⌜err = GoInterface.nil⌝ ∗ connOk conn γ who) ∨ ⌜conn = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
