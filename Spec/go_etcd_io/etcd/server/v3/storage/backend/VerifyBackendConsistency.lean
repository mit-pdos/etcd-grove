/-
## `VerifyBackendConsistency(b, lg, skipSafeRangeBucket, buckets...)` (`verify.go:63-86`): trusted (names only)

**Users.** 2d's `applyAll` (`server.go:982`), `applySnapshot` (`server.go:2295`). **Why it is
true.** `verify.Verify` runs its closure only if `ETCD_VERIFY` names it (`envOk`: unset): a no-op.
**Changes.** From `specs-ref`'s: `envOk` (was `envVerifyOff`). **Margin.** None.
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

/-- **`VerifyBackendConsistency(...)`**: nothing, with verification off. -/
def VerifyBackendConsistency.spec : Prop :=
  ∀ (b : GoInterface) (lg : Loc) (skip : Bool) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency)) (Val #b)) (Val #lg)) (Val #skip))
      (Val #sl))
  {{ RET #(); True }}

end spec

end Backend
end EtcdGrove
end Perennial
