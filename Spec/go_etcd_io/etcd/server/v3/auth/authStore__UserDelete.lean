/-
`authStore.UserDelete` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
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

/-- **`as.UserDelete(r)`** for a request naming `name`: having read the flag `en` (outside
`enabledMu`), the step `userDeleteF en name` (`root` refused with auth enabled, `ErrUserNotFound`,
or the user deleted and the revision bumped). -/
abbrev auth.authStore.UserDelete.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ userDeleteReqIs r name ∗ authOwn M hs ∗ authWR st M P f T ∗ tpAdmin st M ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (userDeleteF en name))⌝ ∗
      (□ ∀ en : Bool, capNextM M hs (stepOf (userDeleteF en name))) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserDelete")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); tpAdmin st M ∗ (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserDeleteResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗ adminOut M hs (stepOf (userDeleteF en name)) noExtra err }}

end spec

end EtcdGrove
end Perennial
