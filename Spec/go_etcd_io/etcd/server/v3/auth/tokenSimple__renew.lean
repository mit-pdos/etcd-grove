/-
`tokenSimple.renew` (`server/auth/simple_token.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
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

/-- `t.renew(ctx, token, revision)`: `(token, nil)`, or `("", ErrAuthFailed)` (auth disabled) or `("", ErrInvalidAuthToken)` (unknown token). What it accepts is below the admin's table (`stLockP`: a live or an expired token, both in `A`); the TTL does not bound it. -/

abbrev auth.tokenSimple.renew.spec : Prop :=
  ∀ (t : Loc) (γ γk : GName) (ctx : GoInterface) (tk : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ isTS t γ γk }}
    (App (App (App (Val (t @!! go.GoType.PointerType tokenSimple.ty @!! go!"renew")) (Val #ctx)) (Val #tk)) (Val #rev))
  {{ (r : GoString) (err : GoInterface), RET (PairV #r #err);
      ⌜err = GoInterface.nil ∧ r = tk⌝ ∨
      ⌜r = go!""⌝ ∗ (errVarIs ErrAuthFailed err ∨ errVarIs ErrInvalidAuthToken err) }}

end spec

end EtcdGrove
end Perennial
