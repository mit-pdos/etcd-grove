/-
`tokenSimple.invalidateUser` (`server/auth/simple_token.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvSimpleToken.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvSimpleToken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `t.invalidateUser(username)`, by the admin (it reads `t.simpleTokenKeeper` without the lock): if enabled, none of `username`'s tokens is allowed any more, live or expired. -/

abbrev auth.tokenSimple.invalidateUser.spec : Prop :=
  ∀ (t : Loc) (γ γk : GName) (A : GMap GoString GoString) (kp : Loc) (u : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ isTS t γ γk ∗ tsAdmin t γ A kp }}
    (App (Val (t @!! go.GoType.PointerType tokenSimple.ty @!! go!"invalidateUser")) (Val #u))
  {{ RET #(); tsAdmin t γ (if kp = null then A else GMap.filter (fun _ v => decide (v ≠ u)) A) kp }}

end spec

end EtcdGrove
end Perennial
