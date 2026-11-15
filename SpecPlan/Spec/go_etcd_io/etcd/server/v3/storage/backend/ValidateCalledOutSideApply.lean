/-
## `ValidateCalledOutSideApply(lg)` (`verify.go:39-46`): trusted (names only)

**Users.** `batchTx.LockOutsideApply`. **Why it is true.** As `ValidateCalledInsideApply`.
**Changes.** `envOk`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`ValidateCalledOutSideApply(lg)`**: nothing, with verification off. -/
def ValidateCalledOutSideApply.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledOutSideApply)) (Val #lg))
  {{ RET #(); True }}

end spec

end Backend
end EtcdGrove
end Perennial
