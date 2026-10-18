/-
`addFeatureGateMetrics(fg, gaugeVec)` (`server.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.features.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `addFeatureGateMetrics(fg, gv)` sets a gauge per feature of the gate and returns: the gate a
`*featuregate.featureGate` (its type assertion to `MutableFeatureGate` holds), the gauge vector
the package's `serverFeatureEnabled` (read-only after `init`: `prometheus.NewGaugeVec` with the
labels `name` and `stage` the calls pass; unit N1, 2026-10-17: `gv.With(…)` panics on a nil
vector or another label set, so an arbitrary `gv`, as stated at N0, made the axiom false). The gate
meets the feature gate's contract (`isFeatureGate`; audit B4b, 2026-10-18: a zero `featureGate`
panics in `GetAll`'s `f.known.Load().(map…)`): its `Enabled` of the server's features returns, so
its `enabled` map is set, and every store of `enabled` follows one of `known` (`New`) or a load
of it (`SetFromMap`, `DeepCopy`; the fields are unexported), so `GetAll` returns `known`'s
features, whose `Enabled` returns. -/
abbrev addFeatureGateMetrics.spec : Prop :=
  ∀ (fg : GoInterface) (gv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜∃ p : Loc, p ≠ null ∧
        fg = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p⌝ ∗
      isFeatureGate fg ∗
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.serverFeatureEnabled ↦□ gv }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics)) (Val #fg))
      (Val #gv))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
