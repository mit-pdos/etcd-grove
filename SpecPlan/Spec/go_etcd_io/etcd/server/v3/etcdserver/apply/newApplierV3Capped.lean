/-
`newApplierV3Capped(base)` (`capped.go:31`): the capped applier over `base` (a zero `BackendQuota` for `Cost`).

**Users.** `uberApplier.restoreAlarms`.

**Proof sketch.** Allocation.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The capped applier over `base`.** -/
def newApplierV3Capped.spec : Prop :=
  ∀ (base : GoInterface) (ls : List Layer) (b aa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ applierAt base ls b aa }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Capped)) (Val #base))
  {{ (v : GoInterface), RET #v; applierAt v (Layer.capped :: ls) b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
