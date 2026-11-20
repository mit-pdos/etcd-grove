/-
What a prometheus metric's methods do (client_golang v1.24.1, the version etcd's `server/go.mod`
pins), as the constructors' specs (`NewCounter`, `NewGauge`, `NewHistogram`) return them: none of
the methods etcd calls panics on the arguments it passes, and none has an effect any verified code
observes. (metric-vecs, 2026-11-19) Moved here from mvcc's `Base.lean`, which defined them for its
own metrics and re-exports them (`export`: `go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec` is
`EtcdGrove.prometheus.metric.counterSpec`), so that prometheus's specs do not depend on mvcc.

(In the namespace `metric`: `EtcdGrove.prometheus.counterSpec` is the vector's counter of
`CounterVec.WithLabelValues`, with fewer methods.)
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus.metric

open Iris Iris.BI

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A prometheus `Counter`: `Inc()` returns, and so does `Add(v)` for a non-negative `v`
(prometheus' `counter.Add` panics on a negative value, "counter cannot decrease in value"; item 8,
2026-10-17: until then `Add(x)` for every `x`, false of the Go code), stated for the arguments the
code passes: `float64(n)` of an unsigned `n` (mvcc's `metricsTxnWrite.End`) and of a non-negative
signed `n` (mvcc's `scheduleCompaction`'s compacted-keys count). -/
def counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ n : w64, {{ True }} (App (Val #(methods c.ty go!"Add" c.v)) (Val #(uint64ToFloat64 n)))
      {{ RET #(); True }}) ∗
    □ (∀ n : w64, ⌜0 ≤ sint.Z n⌝ →
      {{ True }} (App (Val #(methods c.ty go!"Add" c.v)) (Val #(int64ToFloat64 n))) {{ RET #(); True }}))

instance counterSpec_persistent (c : GoInterfaceOk) : Persistent (counterSpec (GF := GF) c) := by
  unfold counterSpec; infer_instance

/-- A prometheus `Gauge`: `Inc()`, `Dec()` and `Add(x)` return. -/
def gaugeSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods g.ty go!"Inc" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods g.ty go!"Dec" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Add" g.v)) (Val #x)) {{ RET #(); True }}))

instance gaugeSpec_persistent (g : GoInterfaceOk) : Persistent (gaugeSpec (GF := GF) g) := by
  unfold gaugeSpec; infer_instance

/-- A prometheus `Histogram`'s `Observe(x)` returns. -/
def histSpec (h : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}))

instance histSpec_persistent (h : GoInterfaceOk) : Persistent (histSpec (GF := GF) h) := by
  unfold histSpec; infer_instance

/-- A prometheus `Gauge`'s `Set(x)` returns. -/
def gaugeSetSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Set" g.v)) (Val #x)) {{ RET #(); True }}))

instance gaugeSetSpec_persistent (g : GoInterfaceOk) : Persistent (gaugeSetSpec (GF := GF) g) := by
  unfold gaugeSetSpec; infer_instance

end preds

end prometheus.metric
end EtcdGrove
end Perennial
