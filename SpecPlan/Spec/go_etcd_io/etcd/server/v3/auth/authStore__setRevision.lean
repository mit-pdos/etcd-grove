/-
## `(*authStore).setRevision(rev)` (internal helper)

**Users.** `AuthEnable` (the stored revision, unchanged), `Recover` (the snapshot's).

**Proof sketch.** `atomic.StoreUint64`: the atomic view moves to the recorded state.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal

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

/-- **`as.setRevision(rev)`** of the recorded state's revision. -/
def authStore.setRevision.spec : Prop :=
  ∀ (st : Loc) (rev : w64) (γ : Cluster) (γa : AuthNames) (i : Nat) (a' : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ wrRec γa i a' ∗ ⌜uint.nat rev = a'.rev⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"setRevision")) (Val #rev))
  {{ RET #(); wrRec γa i a' }}

end spec
end Auth
end EtcdGrove
end Perennial
