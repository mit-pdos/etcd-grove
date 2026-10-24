/-
`authStore.UserGrantRole` (`server/auth/store.go`): the admin side (the auth plan's S4c, 2026-10-24).
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

/-- **`as.UserGrantRole(r)`** for a request naming `user` (within bbolt's key bound: the put
contract's premise) and `role`, the user's roles in the latest state fewer than `2^62` (`sort.Strings`'
bound, after the append): the step `userGrantRoleR user role`. -/
abbrev auth.authStore.UserGrantRole.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (user role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      userGrantRoleReqIs r user role ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ authOwn M hs ∗
      authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜∀ (sta : AuthState) (u : User), histLast M hs sta → sta.users !! user = some u →
        u.length < 2 ^ 62⌝ ∗
      ⌜stepOk M hs (userGrantRoleR user role)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"UserGrantRole")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthUserGrantRoleResponse resp err ∗
      adminOut M hs (userGrantRoleR user role) noExtra err }}

end spec

end EtcdGrove
end Perennial
