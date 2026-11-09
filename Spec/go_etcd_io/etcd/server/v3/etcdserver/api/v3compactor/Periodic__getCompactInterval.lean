/-
## `(*Periodic).getCompactInterval()` (`periodic.go`): translated

**Users.** The periodic loop, `newPeriodic`. **Proof sketch.** Arithmetic on the period (capped at
an hour; the retry interval a tenth of it: non-zero by the period's bound, which `isPeriodic`
keeps). **Changes**: from `specs-ref`'s `Periodic__getCompactInterval.lean`. **Margin.** The value is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`getCompactInterval()`**: some value, without a panic. -/
def Periodic.getCompactInterval.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic p }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getCompactInterval")) (Val #()))
  {{ (d : time.Duration), RET #d; True }}

end spec

end V3compactor
end EtcdGrove
end Perennial
