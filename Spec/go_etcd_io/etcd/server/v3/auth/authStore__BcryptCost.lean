/-
## `(*authStore).BcryptCost()`

**Users.** `EtcdServer.UserAdd`, `UserChangePassword` (`v3_server.go:893,918`, 2c): the cost given
to `bcrypt.GenerateFromPassword`. Snippet: `examples/specreq/auth/admin.go`
(`ReqUserAddThenCheck`).

**Proof sketch.** The read-only field (`authStoreAt`), set by `NewAuthStore` within
`[MinCost, MaxCost]` (an out-of-range cost replaced by `DefaultCost`).

**Changes.** The old spec (`member-auth-facts.md`: the field's points-to) restated over the store
handle, with the range (what makes `GenerateFromPassword` fail only for a long password).

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

/-- **`as.BcryptCost()`**: a cost bcrypt accepts. -/
def authStore.BcryptCost.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"BcryptCost")) (Val #()))
  {{ (c : w64), RET #c; ⌜4 ≤ sint.Z c ∧ sint.Z c ≤ 31⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
