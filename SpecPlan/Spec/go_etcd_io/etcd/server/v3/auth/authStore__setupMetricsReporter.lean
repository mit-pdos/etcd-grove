/-
## `(*authStore).setupMetricsReporter()` (internal helper)

**Users.** `NewAuthStore`.

**Proof sketch.** `reportCurrentAuthRevMu.Lock()` (the package's lock, its invariant in `isPkgInit`: the global closure is one that loads some store's revision atomic), the global replaced by a closure over `as.Revision()` (`authStoreAt`), `Unlock`.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`as.setupMetricsReporter()`**: no observable effect. -/
def authStore.setupMetricsReporter.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"setupMetricsReporter")) (Val #()))
  {{ RET #(); True }}

end spec
end Auth
end EtcdGrove
end Perennial
