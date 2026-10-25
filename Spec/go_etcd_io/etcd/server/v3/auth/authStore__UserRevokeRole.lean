/-
`authStore.UserRevokeRole` (`server/auth/store.go`): the admin side (the auth plan's S4b, 2026-10-24).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.UserRevokeRole(r)`** for a request naming `name` (within bbolt's key bound: the put
contract's premise; the user exists, so the store accepted the name once, but the contract does
not remember it) and `role`: having read the flag `en` (outside `enabledMu`), the step
`userRevokeRoleF en name role`. -/
abbrev auth.authStore.UserRevokeRole.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      userRevokeRoleReqIs r name role ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗
      authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ en : Bool, stepOk M hs (stepOf (userRevokeRoleF en name role))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserRevokeRole")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserRevokeRoleResponse resp err ∗ ∃ en : Bool, enabledVerdict M en ∗
      adminOut M hs (stepOf (userRevokeRoleF en name role)) noExtra err }}

end spec

end EtcdGrove
end Perennial
