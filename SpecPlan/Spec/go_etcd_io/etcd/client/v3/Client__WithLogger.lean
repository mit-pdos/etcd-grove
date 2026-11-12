/-
`(*clientv3.Client).WithLogger` (`client/v3/client.go`).

Users: no user in scope.

Proof sketch: an atomic store of an `isLogger` into `c.lg` (its invariant).

Changes: new (no old spec).

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

/-- `c.WithLogger(lg)`: the logger replaced; `c` returned. -/
def Client.WithLogger.spec : Prop :=
  ∀ (c : Loc) (who : Principal) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientBase c who ∗ Zap.isLogger lg }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"WithLogger")) (Val #lg))
  {{ RET #c; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
