/-
## `(*Periodic).getRetentions()` (`periodic.go`): translated

**Users.** The periodic loop, `newPeriodic`. **Proof sketch.** Arithmetic on the period (capped at
an hour; the retry interval a tenth of it: non-zero by the period's bound, which `isPeriodic`
keeps). **Changes**: from `specs-ref`'s `Periodic__getRetentions.lean`. **Margin.** The value is not stated.
Changes: verify-round (A7 completeness F2): the compactor's handles carry the gate `R` of its `Compactable`
(`compactable c R`: `Compact` is safe once `□ R`, the server's start); `Run` takes `□ R`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3compactor

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

/-- **`getRetentions()`**: some value, without a panic. -/
def Periodic.getRetentions.spec : Prop :=
  ∀ (R : IProp GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic p R }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getRetentions")) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end V3compactor
end EtcdGrove
end Perennial
