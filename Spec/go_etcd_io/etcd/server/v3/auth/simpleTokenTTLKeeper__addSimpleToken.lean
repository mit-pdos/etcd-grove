/-
`(*simpleTokenTTLKeeper).addSimpleToken` (`server/auth/simple_token.go`), as PR etcd#22338
changes it: after inserting the token's expiry, it sets `simpleTokenGauge` to the map's new size
and logs a warning when that size is a multiple of 10000 (if the keeper has a logger).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvSimpleToken.lean`.
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

/-- `tm.addSimpleToken(token)` (the caller holds the provider's lock, which owns the expiry map
`m` and the gauge's state): `token` gets some expiry `e` and the gauge is set to the count of
the new map, `float64(len(m[token := e]))`. -/
abbrev auth.simpleTokenTTLKeeper.addSimpleToken.spec : Prop :=
  ∀ (tm : Loc) (tokens : GoMap) (ttl : time.Duration) (lg : Loc)
    (m : GMap GoString time.Time) (G : w64 → IProp GF) (x : w64) (token : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      keeperFields tm tokens ttl lg ∗ tokens ↦$ m ∗ gaugeModel G ∗ G x }}
    (App (Val (tm @!! go.GoType.PointerType simpleTokenTTLKeeper.ty @!! go!"addSimpleToken"))
      (Val #token))
  {{ RET #(); ∃ e : time.Time, tokens ↦$ (<[token := e]> m) ∗
      G (tokenCount (<[token := e]> m)) }}

end spec

end EtcdGrove
end Perennial
