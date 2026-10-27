/-
`(*prometheus.GaugeVec).With(labels)`: names-only (the server's `start` sets the cluster version gauge). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.github_com.prometheus.client_golang.prometheus.Labels

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `gv.With(labels)` returns the vector's gauge for the labels, whose `Set` returns (names-only;
the server's `start`: `ClusterVersionMetrics.With(…).Set(1)`). Go panics (the vector's
`GetMetricWith` error) unless the map has one entry per label name of the vector and its values
are valid UTF-8: the premise `labelMapOk`, against the vector's label names (`vecLabels`, from its
initializer's fact; D19l (iii), 2026-10-18); the map is read at any fraction and kept. -/
abbrev prometheus.GaugeVec.With.spec : Prop :=
  ∀ (gv : Loc) (labels : Loc) (ls : List GoString) (M : GMap GoString GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      ⌜prometheus.vecLabels gv ls ∧ prometheus.labelMapOk ls M⌝ ∗ labels ↦${dq} M }}
    (App (Val (gv @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.GaugeVec.ty @!! go!"With"))
      (Val #labels))
  {{ (g : GoInterface), RET #g; ∃ gi : GoInterfaceOk, ⌜g = GoInterface.ok gi⌝ ∗
      □ (∀ x : w64, {{ True }} (App (Val #(methods gi.ty go!"Set" gi.v)) (Val #x)) {{ RET #(); True }}) ∗
      labels ↦${dq} M }}

end spec

end EtcdGrove
end Perennial
