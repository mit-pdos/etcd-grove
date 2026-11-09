/-
## `(*authStore).selectPassword(password, hashedPassword)` (assumed: translated names only)

**Users.** `UserAdd`, `UserChangePassword`.

**Why true.** (`auth/store.go:420-426`, untranslated: `bcrypt`, `encoding/base64`) a non-empty `password` with an empty `hashedPassword` (a pre-3.5 entry): `bcrypt.GenerateFromPassword(password, as.bcryptCost)` (`Bcrypt.GenerateFromPassword.spec`: no error for a password of at most 72 bytes and a cost in range, `authStoreAt`); otherwise `base64.StdEncoding.DecodeString(hashedPassword)`, the inverse of `b64` (`hashedPw`'s realization). No panic.

**Changes.** New (the old one was an axiom over the request's shape, `userAddSure`).

**Margin.** The other inputs (an error: `ErrNoPasswordUser` at the callers) are not stated: `authReqAt` rules them out.
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

/-- **`as.selectPassword(p, hp)`** for the forms `authReqAt` allows: a fresh bcrypt hash of `pw`. -/
def authStore.selectPassword.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (p hp pw : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗
      ⌜(hp ≠ [] ∧ hashedPw hp pw) ∨ (hp = [] ∧ p = pw ∧ p ≠ [] ∧ pw.length ≤ 72)⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"selectPassword")) (Val #p)) (Val #hp))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err); ⌜err = GoInterface.nil⌝ ∗
      ∃ hb : List w8, h ↦* hb ∗ ⌜Bcrypt.hashOf hb pw⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
