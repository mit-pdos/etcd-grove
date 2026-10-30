/-
`authStore.RoleRevokePermission` (`server/auth/store.go`): the admin side (the auth plan's S4b, 2026-10-24).
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

/-- **`as.RoleRevokePermission(r)`** for a request naming `role` (within bbolt's key bound) and
the range `[key, rangeEnd)`: the step `roleRevokePermissionR role key rangeEnd`. -/
abbrev auth.authStore.RoleRevokePermission.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (role key rangeEnd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleRevokePermissionReqIs r role key rangeEnd ∗ ⌜role.length ≤ backend.maxKeySize⌝ ∗
      authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (roleRevokePermissionR role key rangeEnd)⌝ ∗ capNextM M hs (roleRevokePermissionR role key rangeEnd) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleRevokePermission")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthRoleRevokePermissionResponse resp err ∗
      adminOut M hs (roleRevokePermissionR role key rangeEnd) noExtra err }}

end spec

end EtcdGrove
end Perennial
