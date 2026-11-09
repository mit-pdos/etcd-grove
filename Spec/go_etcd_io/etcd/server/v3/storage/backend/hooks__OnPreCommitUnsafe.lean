/-
## `hooks.OnPreCommitUnsafe(tx)` (`hooks.go:30-32`): translated

**Users.** The backend's commit (`unsafeCommit`, `batch_tx.go:383`) through the `Hooks` value.
**Proof sketch.** `h.onPreCommitUnsafe(tx)`. **Changes.** Unchanged. **Margin.** None.
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

/-- **`h.OnPreCommitUnsafe(tx)`**: `f(tx)`, by the caller's triple of `f`. -/
def hooks.OnPreCommitUnsafe.spec : Prop :=
  ∀ (h : go_etcd_io.etcd.server.v3.storage.backend.hooks) (tx : GoInterface) (Φ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ WP (App (Val #h.onPreCommitUnsafe') (Val #tx)) {{ Φ }} ⊢
  WP (App (Val (h @!! go_etcd_io.etcd.server.v3.storage.backend.hooks.ty @!! go!"OnPreCommitUnsafe")) (Val #tx)) {{ Φ }}

end spec

end Backend
end EtcdGrove
end Perennial
