/-
## `(*authStore).Close()`

**Users.** `EtcdServer.Cleanup` (`server.go:953`, 2e: `srvClosers`). Snippet:
`examples/specreq/auth/boot.go` (`ReqCloseAfterStop`).

**Proof sketch.** `enabledMu.Lock()`; auth on: the provider's `disable()` (the simple provider's keeper
stopped and waited for, its tokens dropped); `nil`.

**Changes.** The old spec (`authCloseOk`) needed the store's closer; nothing is needed: a later reader
sees tokens refused (`ErrInvalidAuthToken`, allowed), a later writer's `AuthEnable` restarts the
keeper.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`as.Close()`**: `nil`. -/
def authStore.Close.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
