/-
`simpleTokenTTLKeeper.stop` (`server/auth/simple_token.go`), pr-verify etcd#22560 (2026-10-16). Lean-first (no Rocq
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

/-- `tm.stop()` (names only: a `select` on the keeper's channels): returns once the keeper's goroutine has exited. A postulate. -/

abbrev auth.simpleTokenTTLKeeper.stop.spec : Prop :=
  ∀ (t k : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperRO t k }}
    (App (Val (k @!! go.GoType.PointerType simpleTokenTTLKeeper.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
