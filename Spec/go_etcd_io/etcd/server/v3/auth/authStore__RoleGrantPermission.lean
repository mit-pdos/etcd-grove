/-
`authStore.RoleGrantPermission` (`server/auth/store.go`), as PR etcd#21845 changes it
(`pr-verify/etcd-21845`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvRole

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.RoleGrantPermission(r)`, the request `r` granting `p` (at `pp`) to role `name`, the
backend's roles `m` sorted by key and the role short (`< 2^62` permissions): the caller's `W`
back, and the roles `m'`, sorted by key, where
- on success (`err = nil`) the request had a permission, the role existed, and its permissions
  are granted `p` (`GrantSpec`: the first one on `p`'s key and range end takes `p`'s type, or,
  if there is none, `p` is added and the list sorted by key);
- on an error, the roles are unchanged;
- a missing role is an error.
Only the *first* permission on `p`'s range is updated: a role already holding two on one range (as
an etcd without the PR's fix may have stored) keeps the later ones (`grantSpec_mem` needs
`NoDupRanges`). The result is about the stored role, not the permission cache
(`refreshRangePermCache` is a postulate). -/
abbrev auth.authStore.RoleGrantPermission.spec : Prop :=
  ∀ (st : Loc) (R W H : IProp GF) (Roles : RolesM → IProp GF) (m : RolesM) (r : Loc)
    (name : GoString) (pp : Loc) (p : PermM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗
      authWriteInv st W H Roles ∗ grantGlobals ∗ grantReqOk r name pp p ∗ W ∗ Roles m ∗
      ⌜rolesSorted m ∧ ∀ ps, m name = some ps → ps.length < 2 ^ 62⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleGrantPermission")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); W ∗ ∃ m' : RolesM, Roles m' ∗
      ⌜rolesSorted m' ∧
        (err = GoInterface.nil → pp ≠ null ∧
          ∃ ps ps', m name = some ps ∧ GrantSpec ps ps' p ∧ m' = rolesSet m name ps') ∧
        (err ≠ GoInterface.nil → m' = m) ∧
        (m name = none → err ≠ GoInterface.nil)⌝ }}

end spec

end EtcdGrove
end Perennial
