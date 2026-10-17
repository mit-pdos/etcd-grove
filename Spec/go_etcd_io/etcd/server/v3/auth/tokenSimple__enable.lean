/-
`tokenSimple.enable` (`server/auth/simple_token.go`), as PR etcd#22338 leaves it (branch pr-verify/etcd-22338; the spec is pr-verify/etcd-22560's, without its `expiredTokens`). Lean-first (no Rocq
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `t.enable()`, by the admin: a keeper (a new one, with its goroutine, if there was none). -/

abbrev auth.tokenSimple.enable.spec : Prop :=
  ∀ (t : Loc) (γ γk : GName) (A : GMap GoString GoString) (kp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ isTS t γ γk ∗ tsAdmin t γ A kp }}
    (App (Val (t @!! go.GoType.PointerType tokenSimple.ty @!! go!"enable")) (Val #()))
  {{ (kp' : Loc), RET #(); tsAdmin t γ A kp' ∗ ⌜kp' ≠ null⌝ ∗ ⌜kp ≠ null → kp' = kp⌝ }}

end spec

end EtcdGrove
end Perennial
