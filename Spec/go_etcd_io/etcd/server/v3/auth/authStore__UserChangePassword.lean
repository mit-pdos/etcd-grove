/-
`authStore.UserChangePassword` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (the
write side's contracts) and `Steps.lean` (the model's steps).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

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

/-- **`as.UserChangePassword(r)`** for a request naming `name` (within bbolt's key bound: the
rewritten record's key; a user of the name exists when it is written, so its key was accepted
before, which the write contract does not record): the step
`userChangePasswordF name` (`ErrUserNotFound`, or the record rewritten with the same roles and the
revision bumped), or `ErrNoPasswordUser`. -/
abbrev auth.authStore.UserChangePassword.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userChangePasswordReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWR st M P f T ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userChangePasswordF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserChangePassword")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); tpAdmin st M ∗ (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserChangePasswordResponse resp err ∗ adminOut M hs (stepOf (userChangePasswordF name)) (fun e => e = .noPasswordUser) err }}

end spec

end EtcdGrove
end Perennial
