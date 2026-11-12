/-
## `(*authStore).GenTokenPrefix()`

**Users.** `EtcdServer.Authenticate` (`v3_server.go:865`, 2c): the prefix the proposal carries.
Snippet: `examples/specreq/auth/token.go` (`ReqAuthenticateApply`).

**Proof sketch.** The provider's `genTokenPrefix()` (`tokenProviderAt`'s contract: the simple
provider's 16 random letters, `tokenSimple.genTokenPrefix`; `""` for the others). Any goroutine.

**Changes.** Unchanged in substance.

**Margin.** The prefix is not stated (nothing relies on it: the entry index makes the token unique).
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

/-- **`as.GenTokenPrefix()`**: some string, or an error; no panic. -/
def authStore.GenTokenPrefix.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"GenTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err); True }}

end spec
end Auth
end EtcdGrove
end Perennial
