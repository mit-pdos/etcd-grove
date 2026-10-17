/-
The simple-token provider's TTL keeper (`server/auth/simple_token.go`) and the token-count gauge
of PR etcd#22338 (`simpleTokenGauge`, `metrics.go`; branch `pr-verify/etcd-22338`). Lean-first (no
Rocq counterpart); see `notes/pr-verify/etcd-22338.md`.

**The gauge** (`gaugeModel G`): `simpleTokenGauge` holds, read-only, a prometheus `Gauge` whose
`Set(y)` takes the gauge's state from `G x` to `G y`. `G` is the specs' parameter: prometheus is
translated names-only, so what the gauge's value is lives in the caller's choice of `G` (a ghost
variable holding the last value set, for the PR's claim "the gauge shows the number of tokens").
Nothing is assumed of `Set` beyond that.

**The keeper** `tm` (`keeperRO tm tokens ttl lg`): its fields `tokens` (the expiry map),
`simpleTokenTTL` and `lg` are read-only after `enable` builds it; the map's contents are the
caller's (under the provider's `simpleTokensMu`, which the keeper's `mu` points to).

**The count** `tokenCount m`: what the PR's code passes to `Set` for the map `m`,
`float64(len(m))` (`int64ToFloat64`, an uninterpreted conversion: Perennial's floats are bit
patterns).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&tm.<f>` (a `*simpleTokenTTLKeeper`) -/
abbrev kF (f : GoString) (tm : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper f tm

/-- `&t.<f>` (a `*tokenSimple`) -/
abbrev tsF (f : GoString) (t : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.tokenSimple f t

/-- The value the PR's code sets the gauge to for the expiry map `m`: `float64(len(m))`. -/
abbrev tokenCount {V : Type} (m : GMap GoString V) : w64 :=
  int64ToFloat64 (W64 (GMap.size m))

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The gauge** `simpleTokenGauge` (read-only) and its `Set` for the gauge state `G`. -/
def gaugeModel (G : w64 → IProp GF) : IProp GF :=
  iprop(∃ g : GoInterfaceOk, globalAddr simpleTokenGauge ↦□ GoInterface.ok g ∗
    □ (∀ x : w64, ∀ y : w64, {{ G x }} (App (Val #(methods g.ty go!"Set" g.v)) (Val #y))
      {{ RET #(); G y }}))

instance gaugeModel_persistent (G : w64 → IProp GF) : Persistent (gaugeModel G) := by
  unfold gaugeModel; infer_instance

/-- **The keeper** `tm`'s read-only fields: the expiry map `tokens`, the TTL, the logger (nil or
not: `addSimpleToken` tests it). -/
def keeperRO (tm : Loc) (tokens : GoMap) (ttl : time.Duration) (lg : Loc) : IProp GF :=
  iprop(kF go!"tokens" tm ↦□ tokens ∗ kF go!"simpleTokenTTL" tm ↦□ ttl ∗ kF go!"lg" tm ↦□ lg)

instance keeperRO_persistent (tm : Loc) (tokens : GoMap) (ttl : time.Duration) (lg : Loc) :
    Persistent (keeperRO (GF := GF) tm tokens ttl lg) := by
  unfold keeperRO; infer_instance

end defs

end auth
end EtcdGrove
end Perennial
