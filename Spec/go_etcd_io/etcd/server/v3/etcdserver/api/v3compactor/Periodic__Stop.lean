/-
## `(*Periodic).Stop()` (`periodic.go`): translated

**Users.** `Cleanup` (once).
**Proof sketch.** cancels the loop's context (the loop exits at its next check; a `Compact` in flight is answered by the server, stopped or not): under the compactor's mutex or its context; the loop's calls through
`revGetter` and `compactable` (the handle's). **Changes**: from `specs-ref`'s `Periodic__Stop.lean`:
no run token (any number of calls is safe). **Margin.** None.
Changes: verify-round (A7 completeness F2): the compactor's handles carry the gate `R` of its `Compactable`
(`compactable c R`: `Compact` is safe once `□ R`, the server's start); `Run` takes `□ R`.
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

/-- **`Stop`**: cancels the loop's context. -/
def Periodic.Stop.spec : Prop :=
  ∀ (R : IProp GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic p R }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end V3compactor
end EtcdGrove
end Perennial
