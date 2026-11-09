/-
## `(*authStore).commitRevision(tx)` (internal helper)

**Users.** Every admin step that changes the state but `AuthEnable`; `NewAuthStore` (a fresh backend).

**Proof sketch.** `atomic.AddUint64(&as.revision, 1)`: the linearization point, the step's state `a'` recorded as the `(i+1)`-th (the history's authority in the store's invariant, with the writer's `authReached γ a'`), the atomic view at it; `tx.UnsafeSaveAuthRevision(as.Revision())` (4b: the revision written into the batch transaction).

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.commitRevision(tx)`** in a step from `a` to `a'` (`a'` the transaction's state with the
revision bumped): `a'` recorded, the revision written. -/
def authStore.commitRevision.spec : Prop :=
  ∀ (st : Loc) (tx : GoInterface) (γ : Cluster) (γa : AuthNames) (i : Nat) (a a' b : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ wrStep γa i a a' ∗ txAt tx b ∗ authReached γ a' ∗
      ⌜a'.rev = a.rev + 1 ∧ a' = { b with rev := a'.rev } ∧ validPerms a' ∧ recordsFit a'⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"commitRevision")) (Val #tx))
  {{ RET #(); wrRec γa i a' ∗ txAt tx a' }}

end spec
end Auth
end EtcdGrove
end Perennial
