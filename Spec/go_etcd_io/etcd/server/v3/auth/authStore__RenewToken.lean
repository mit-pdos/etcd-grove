/-
`authStore.RenewToken` (`server/auth/store.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
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

/-- `as.RenewToken(ctx, token)`: a token and an error (the token "" on an error); it keeps the caller's reader resources (a slot of `enabledMu`, the backend's read resource `R`). Its call of `tokenProvider.invalidateUser` is the admin's (`tokenProviderOk`), which a request goroutine is not. -/

abbrev auth.authStore.RenewToken.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterface) (tk : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st ∗ R }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RenewToken")) (Val #ctx)) (Val #tk))
  {{ (r : GoString) (err : GoInterface), RET (PairV #r #err);
      enabledRd st ∗ R ∗ (⌜err = GoInterface.nil⌝ ∨ ⌜r = go!""⌝) }}

end spec

end EtcdGrove
end Perennial
