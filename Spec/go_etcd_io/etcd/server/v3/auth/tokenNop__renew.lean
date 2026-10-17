/-
`tokenNop.renew` (`server/auth/nop.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
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

/-- `t.renew(ctx, token, revision)` of the provider of a cluster without auth: `("", ErrAuthFailed)`. -/

abbrev auth.tokenNop.renew.spec : Prop :=
  ∀ (t : Loc) (ctx : GoInterface) (tk : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (App (App (Val (t @!! go.GoType.PointerType tokenNop.ty @!! go!"renew")) (Val #ctx)) (Val #tk)) (Val #rev))
  {{ (err : GoInterface), RET (PairV #(go!"") #err); errVarIs ErrAuthFailed err }}

end spec

end EtcdGrove
end Perennial
