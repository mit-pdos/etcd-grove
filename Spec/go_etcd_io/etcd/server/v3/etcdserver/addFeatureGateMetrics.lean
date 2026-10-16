/-
`addFeatureGateMetrics(fg, gaugeVec)` (`server.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

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
`*featuregate.featureGate` (its type assertion to `MutableFeatureGate` holds). -/
abbrev addFeatureGateMetrics.spec : Prop :=
  ∀ (fg : GoInterface) (gv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜∃ p : Loc, p ≠ null ∧
        fg = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics)) (Val #fg))
      (Val #gv))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
