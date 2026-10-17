/-
`tokenJWT.info` (`server/v3/auth/jwt.go`; PR etcd#21909: a verify-only provider returns the store's
revision, not the token's claim). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvJWT.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvJWT

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

/-- `t.info(ctx, token, rev)` of a JWT provider (`jwtProviderRO t vo`): `(nil, false)`, or an auth
info (read-only, not nil) and `true`; a verify-only provider's info has the revision `rev` (the
store's, `authInfoFromToken` passes `as.Revision()`), whatever the token's `revision` claim. -/
abbrev auth.tokenJWT.info.spec : Prop :=
  ∀ (t : Loc) (vo : Bool) (ctx : GoInterface) (token : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ jwtProviderRO t vo }}
    (App (App (App (Val (t @!! go.GoType.PointerType tokenJWT.ty @!! go!"info")) (Val #ctx))
      (Val #token)) (Val #rev))
  {{ (a : Loc) (ok : Bool), RET (PairV #a #ok); authInfoRO a ∗ jwtInfoOk vo rev a ok }}

end spec

end EtcdGrove
end Perennial
