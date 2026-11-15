/-
`clientv3.isContextError` (`client/v3/retry_interceptor.go`).

Users: the unary interceptor, `isSafeRetry`.

Proof sketch: `status.Code(err)` (2a): `Canceled` or `DeadlineExceeded` only for errors of an
indefinite kind (a context's, a status of those codes; no definite etcd error has them).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/isContextError.lean`.

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

/-- `isContextError(err)`: true only for an error that settles nothing. -/
def isContextError.spec : Prop :=
  ∀ (err : GoInterface) (k : CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ callErr err k }}
    (App (Val (@! go_etcd_io.etcd.client.v3.isContextError)) (Val #err))
  {{ (b : Bool), RET #b; ⌜b = true → k.indefinite = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
