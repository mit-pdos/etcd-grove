/-
`simpleTokenTTLKeeper.addSimpleToken` (`server/auth/simple_token.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
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

/-- `tm.addSimpleToken(token)` (the caller holds `t.simpleTokensMu`): the keeper's deadline map, kept. -/

abbrev auth.simpleTokenTTLKeeper.addSimpleToken.spec : Prop :=
  ∀ (k : Loc) (d : time.Duration) (tk : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperMap k ∗ kF go!"simpleTokenTTL" k ↦□ d }}
    (App (Val (k @!! go.GoType.PointerType simpleTokenTTLKeeper.ty @!! go!"addSimpleToken")) (Val #tk))
  {{ RET #(); keeperMap k }}

end spec

end EtcdGrove
end Perennial
