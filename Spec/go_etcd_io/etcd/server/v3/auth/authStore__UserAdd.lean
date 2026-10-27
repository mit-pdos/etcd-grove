/-
`authStore.UserAdd` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
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

/-- **`as.UserAdd(r)`** for a request naming `name` (within bbolt's key bound,
`issues/etcd-auth-useradd-long-name-fatal.md`), from the admin side's authority `hs` with the
write resource and the batch lock's critical-section contract: the step `userAddF name`
(`adminOut`: the user added and the revision bumped, or `ErrUserEmpty`/`ErrUserAlreadyExist`), or
`ErrNoPasswordUser` when the password cannot be selected; a fresh response if it succeeded. -/
abbrev auth.authStore.UserAdd.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userAddReqIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userAddF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserAddResponse resp err ∗ adminOut M hs (stepOf (userAddF name)) (fun e => e = .noPasswordUser) err }}

/-- **`as.UserAdd(r)` of a request whose password choice cannot fail** (`userAddSure r`: no
password, or an empty `Password` with a base64-encoded `HashedPassword`, the server's own form):
as `UserAdd.spec`, without `ErrNoPasswordUser`, so the outcome is the step's alone (`noExtra`; the
auth plan's E2u, 2026-10-26: the apply thread's mode-`on` step is then determinate). -/
abbrev auth.authStore.UserAdd.specSure : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userAddReqIs r name ∗ userAddSure r ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (stepOf (userAddF name))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserAdd")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserAddResponse resp err ∗ adminOut M hs (stepOf (userAddF name)) noExtra err }}

end spec

end EtcdGrove
end Perennial
