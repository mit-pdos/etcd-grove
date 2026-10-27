/-
`authStore.selectPassword` (`server/auth/store.go`): names only, the trust boundary (it hashes
with `golang.org/x/crypto/bcrypt` or decodes with `encoding/base64`, neither translated). The
auth plan's S4 (2026-10-24): `UserAdd` and `UserChangePassword` store its result as the user's
password, which the model does not keep. Lean-first (no Rocq counterpart).
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
error) and an error, which is `nil` when `password` is empty and `hashedPassword` is the standard
base64 encoding of some bytes (`stdB64Enc`; the auth plan's E2u, 2026-10-26). Why that is true of
the Go code: with `password == ""` the function returns `base64.StdEncoding.DecodeString(
hashedPassword)`, and `DecodeString` of a string `StdEncoding.EncodeToString` produced decodes
without an error (the encoding emits only the alphabet's characters, padded to a multiple of 4, which
is exactly what the decoder accepts). Otherwise the error is any (bcrypt's
`GenerateFromPassword`, a decoding of other text). -/
abbrev auth.authStore.selectPassword.spec : Prop :=
  ∀ (st : Loc) (password hashed : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜st ≠ null⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"selectPassword"))
      (Val #password)) (Val #hashed))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err); ∃ bs : GoString, b ↦*□ bs ∗
      ⌜password = [] → (∃ x : List w8, hashed = stdB64Enc x) → err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
