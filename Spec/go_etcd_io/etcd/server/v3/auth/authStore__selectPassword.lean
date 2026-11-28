/-
`authStore.selectPassword` (`server/auth/store.go`): the auth plan's S4 (2026-10-24): `UserAdd` and
`UserChangePassword` store its result as the user's password, which the model does not keep.
Names only (the trust boundary) until prove-authcrypto (2026-11-21): translated with its body and
proved over bcrypt's `GenerateFromPassword` (the trust boundary) and base64's `DecodeString`
(proved, `Proof/encoding/base64/`, `StdEncoding`'s through the package fact `stdDecInit`). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.selectPassword(password, hashedPassword)`: a hash (a fresh slice, read-only; `nil` on an
error) and an error, `nil` exactly when `selectPwOk password hashed` (nomode D3 follow-up (a),
2026-11-28; until then only "`nil` for an empty `password` and a `hashedPassword` the standard base64
encoding of some bytes"). With `password != ""` and `hashedPassword == ""` the function returns
`bcrypt.GenerateFromPassword([]byte(password), as.bcryptCost)`, which errs iff the password is over 72
bytes or the cost over `MaxCost` (its axiom), and the store's cost is at most `MaxCost` (the pre's
`sint.Z c ≤ 31`: `NewAuthStore` replaces a cost out of range by `DefaultCost`; callers have it from
`authInv`, `authInv_bcryptCost`); otherwise `base64.StdEncoding.DecodeString(hashedPassword)`, which
errs iff `stdDecOk` fails (proved, `Proof/encoding/base64/`). The pre has the store's read-only
`bcryptCost` (prove-authcrypto, 2026-11-21; ledger 2026-11-21). -/
abbrev auth.authStore.selectPassword.spec : Prop :=
  ∀ (st : Loc) (password hashed : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜st ≠ null⌝ ∗
      ∃ c : w64, aF go!"bcryptCost" st ↦□ c ∗ ⌜sint.Z c ≤ 31⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"selectPassword"))
      (Val #password)) (Val #hashed))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err); ∃ bs : GoString, b ↦*□ bs ∗
      ⌜err = GoInterface.nil ↔ selectPwOk password hashed⌝ }}

end spec

end EtcdGrove
end Perennial
