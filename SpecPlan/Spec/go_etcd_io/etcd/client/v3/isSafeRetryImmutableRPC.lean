/-
`clientv3.isSafeRetryImmutableRPC` (`client/v3/retry.go`).

Users: the retry interceptor (1c: whether a repeatable call may be resent).

Proof sketch: `rpctypes.Error`, `errors.As`, `status.FromError` (2a's specs over `callErr`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/isSafeRetryImmutableRPC.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: the code also retries a status `Unavailable` that is not etcd's; a read may be resent whatever the answer (its update is persistent), so the spec says only what the interceptor's liveness would use.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `isSafeRetryImmutableRPC(err)`: true at least for a request that never left the client. -/
def isSafeRetryImmutableRPC.spec : Prop :=
  ∀ (err : GoInterface) (k : CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ callErr err k }}
    (App (Val (@! go_etcd_io.etcd.client.v3.isSafeRetryImmutableRPC)) (Val #err))
  {{ (b : Bool), RET #b; ⌜k = .notSent → b = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
