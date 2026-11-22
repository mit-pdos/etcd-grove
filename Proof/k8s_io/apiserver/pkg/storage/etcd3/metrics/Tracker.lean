/-
The etcd3 store's pre-materialized latency tracker (prove-metrics, 2026-11-21): what
`metrics.NewEtcdMetricsTracker`'s trust-boundary spec gives of the `*OperationLatencyTracker` it
stores in `Get`, and what `OperationLatencyTracker.Record`'s takes (apiserver `9c4ec15b8038`,
`metrics.go:360-398`; names-only).

`latencyTrackerOk lt` (opaque, pure, so persistent): `lt` was built by
`NewOperationLatencyTracker(verb, gr)` (inside `NewEtcdMetricsTracker(gr)`), with valid UTF-8
labels: its `latency` and `requests` are the metrics `WithLabelValues` returned for them, and
nothing writes its (unexported) fields afterwards. Until then `Record`'s spec took any non-nil
`t`, and a zero `OperationLatencyTracker` panics in `Record` (`t.latency` is a nil interface):
`examples/premisefix/latencytracker`. Only the two specs state it, as `prometheus.vecLabels` for
the metric vectors.
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3.metrics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The `*OperationLatencyTracker` `lt` is one `NewEtcdMetricsTracker` built (see the file header).
Opaque: only `NewEtcdMetricsTracker`'s and `OperationLatencyTracker.Record`'s trust-boundary specs
state it. -/
opaque metrics.latencyTrackerOk (lt : Loc) : Prop

end EtcdGrove
end Perennial
