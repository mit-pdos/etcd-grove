/-
`tokenSimple.assignSimpleTokenToUser` (`server/auth/simple_token.go`), as PR etcd#22338 leaves it (branch pr-verify/etcd-22338; the spec is pr-verify/etcd-22560's, without its `expiredTokens`). Lean-first (no Rocq
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

/-- `t.assignSimpleTokenToUser(username, token)`, by the admin, of a token it has not allowed (else the code panics: the token is live): allowed for `username`, if enabled. -/

abbrev auth.tokenSimple.assignSimpleTokenToUser.spec : Prop :=
  ∀ (t : Loc) (γ γk : GName) (A : GMap GoString GoString) (kp : Loc) (u tk : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ isTS t γ γk ∗ tsAdmin t γ A kp ∗ ⌜A !! tk = none⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType tokenSimple.ty @!! go!"assignSimpleTokenToUser")) (Val #u)) (Val #tk))
  {{ RET #(); tsAdmin t γ (if kp = null then A else GMap.insert tk u A) kp }}

end spec

end EtcdGrove
end Perennial
