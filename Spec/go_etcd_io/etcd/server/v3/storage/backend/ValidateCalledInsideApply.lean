/-
## `ValidateCalledInsideApply(lg)` (`verify.go:30-37`): trusted (names only)

**Users.** `batchTx.LockInsideApply`. **Why it is true.** `verifyLockEnabled()` is false with
`ETCD_VERIFY` unset (`envOk`): returns at once. **Changes.** `envOk`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`ValidateCalledInsideApply(lg)`**: nothing, with verification off. -/
def ValidateCalledInsideApply.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideApply)) (Val #lg))
  {{ RET #(); True }}

end spec

end Backend
end EtcdGrove
end Perennial
