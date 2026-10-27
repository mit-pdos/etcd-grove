/-
`authStore.RoleDelete` (`server/auth/store.go`): the admin side (the auth plan's S4b, 2026-10-24).
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

/-- **`as.RoleDelete(r)`** for a request naming `role`: having read the flag `en` (outside
`enabledMu`), the step `roleDeleteF en role` (`root` refused with auth enabled, `ErrRoleNotFound`, or
the role deleted and revoked from every user, the revision bumped). Each user who had the role is
put back, so every stored user's name is within bbolt's key bound (`UserAdd` put it under that
bound, but the read contract does not remember it: `issues/etcd-auth-useradd-long-name-fatal.md`). -/
abbrev auth.authStore.RoleDelete.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleDeleteReqIs r role ∗ authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (roleDeleteF en role))⌝ ∗
      ⌜∀ s : AuthState, histLast M hs s → ∀ n : GoString, (s.users !! n).isSome →
        n.length ≤ backend.maxKeySize⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleDelete")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthRoleDeleteResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗
      adminOut M hs (stepOf (roleDeleteF en role)) noExtra err }}

end spec

end EtcdGrove
end Perennial
