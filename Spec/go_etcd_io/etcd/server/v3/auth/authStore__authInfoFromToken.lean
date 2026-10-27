/-
`authStore.authInfoFromToken` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.authInfoFromToken(ctx, token)`: the token provider's `info` at the store's revision; an
accepted token's info is bound to it (`infoBound`; the auth plan's S5). -/

abbrev auth.authStore.authInfoFromToken.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (ctx : GoInterface) (token : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"authInfoFromToken")) (Val #ctx)) (Val #token))
  {{ (a : Loc) (ok : Bool), RET (PairV #a #ok); authInfoRO a ∗
      (if ok then infoBound M token a else iprop(True)) }}

end spec

end EtcdGrove
end Perennial
