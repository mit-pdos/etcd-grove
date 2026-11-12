/-
## `newPeriodic(lg, clock, h, rg, c)` (`periodic.go`): translated

**Users.** `New`. **Proof sketch.** A struct literal, a cancellable context
and the revisions' buffer of `getRetentions()` capacity (`period / (period / 10) + 1`: a period below 10ns in absolute value divides by zero, the premise).
**Changes**: from `specs-ref`'s `newPeriodic.lean`. **Margin.** None.
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

/-- **A periodic compactor.** -/
def newPeriodic.spec : Prop :=
  ∀ (R : IProp GF) (lg : Loc) (clk : GoInterface) (h : time.Duration) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ Zap.isLogger lg ∗ clockOk clk ∗ revGetter rg ∗ compactable c R ∗ ⌜10 ≤ sint.Z h ∨ sint.Z h ≤ -10⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic)) (Val #lg)) (Val #clk)) (Val #h)) (Val #rg)) (Val #c))
  {{ (p : Loc), RET #p; isPeriodic p R }}

end spec

end V3compactor
end EtcdGrove
end Perennial
