/-
`simpleTokenTTLKeeper.run` (`server/auth/simple_token.go`), as PR etcd#22338 leaves it (branch pr-verify/etcd-22338; the spec is pr-verify/etcd-22560's, without its `expiredTokens`). Lean-first (no Rocq
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

/-- `go tm.run()` (a `time.Ticker` loop; PR etcd#22338 sets the gauge to the deadline map's size after each sweep): the keeper's goroutine, given the provider, the keeper's read-only fields, its membership in the provider's keepers (so its deadline map is in the lock) and its two channels; it does not panic. Unfinished (`sorry`). -/

abbrev auth.simpleTokenTTLKeeper.run.spec : Prop :=
  ∀ (t : Loc) (γ γk : GName) (k : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ isTS t γ γk ∗ keeperRO t k ∗ k ↪[γk]□ () ∗ keeperChans k }}
    (App (Val (k @!! go.GoType.PointerType simpleTokenTTLKeeper.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
