/-
`authStore.CheckPassword` (`server/auth/store.go`): the password check of the request side (the auth
plan's E2j, 2026-10-26). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/Reads.lean` (`passwordChecked`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Reads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.CheckPassword(username, password)`** with a reader slot of `enabledMu` and of `beMu` and
the backend's read resource `R` (a request's, as the permission checks'): `IsAuthEnabled`, the
user and the revision under the locked read transaction, then bcrypt's comparison of the stored
hash outside the lock; the answer `passwordChecked` (the revision of a recorded state that has the
user, auth enabled), the slots and `R` kept. -/
abbrev auth.authStore.CheckPassword.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (username password : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      enabledRd st M ∗ beRd st R M ∗ R }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"CheckPassword"))
      (Val #username)) (Val #password))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err); enabledRd st M ∗ beRd st R M ∗ R ∗
      passwordChecked M username rev err }}

end spec

end EtcdGrove
end Perennial
