/-
What a prometheus gauge is in memory (client_golang v1.24.1, `gauge.go`): a `*gauge` whose value
cell is in an invariant, since every access to it is atomic (`sync/atomic`: `Set`, `Add`, `Write`).
The constructors' specs return it (`NewGauge`, and `GaugeVec.WithLabelValues` besides its
`metric.gaugeSpec`); the methods' specs are proved over the real bodies
(`Proof/.../prometheus/gauge__*.lean`). (A counter's struct is not translated: its `createdTs` field's
package, `timestamppb`, would bring two trust-boundary axioms of its names-only initializer.) (prove-ps2-metrics, 2026-11-22; agreed with prom-registry on #15)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus.metric

open Iris Iris.BI

/-- The invariant namespace of the metrics' value cells. -/
def metricN : Namespace := nroot.@"prometheus_metric"

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&g.valBits` of a `*gauge` -/
abbrev gaugeBits (l : Loc) : Loc :=
  structFieldRef github_com.prometheus.client_golang.prometheus.gauge go!"valBits" l

end fields

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The gauge at `l`: its value's bits in an invariant (persistent). -/
def gaugeCell (l : Loc) : IProp GF :=
  iprop(inv metricN (∃ b : w64, gaugeBits l ↦ b))

/-- `g` is a `*gauge` (`gauge.go`) whose value cell is in an invariant. -/
def isGauge (g : GoInterfaceOk) : IProp GF :=
  iprop(∃ l : Loc, ⌜g =
      ⟨go.GoType.PointerType github_com.prometheus.client_golang.prometheus.gauge.ty, #l⟩⌝ ∗
    gaugeCell l)

instance gaugeCell_persistent (l : Loc) : Persistent (gaugeCell (GF := GF) l) := by
  unfold gaugeCell; infer_instance
instance isGauge_persistent (g : GoInterfaceOk) : Persistent (isGauge (GF := GF) g) := by
  unfold isGauge; infer_instance

end preds

end prometheus.metric
end EtcdGrove
end Perennial
