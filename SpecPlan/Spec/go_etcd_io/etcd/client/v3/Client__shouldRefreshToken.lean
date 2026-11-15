/-
`(*clientv3.Client).shouldRefreshToken` (`client/v3/retry_interceptor.go`).

Users: the unary interceptor.

Proof sketch: a configured token: `false`. `rpctypes.Error(err)` (2a's rpctypes law over `callErr`)
compared by `errors.Is` with `ErrUserEmpty`, `ErrInvalidAuthToken`, `ErrAuthOldRevision` (W0's
`errorsIs_errVal`): true only for those.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__shouldRefreshToken.lean`.

Margin: whether it is true for them (the bundle, `retryAuth`) is not stated.
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

/-- `c.shouldRefreshToken(err, opts)`: true only for a token refusal. -/
def Client.shouldRefreshToken.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (err : GoInterface) (k : CallErr) (p : Loc)
    (o : RetryOptsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ callErr err k ∗ optionsAt p o }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"shouldRefreshToken")) (Val #err)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = true → ∃ e, k = .etcd e ∧ errRetryAuth e = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
