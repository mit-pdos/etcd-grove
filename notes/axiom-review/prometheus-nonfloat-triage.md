# The prometheus and metrics axioms that need no float arithmetic (claim #27, prove-metrics, 2026-11-21)

Claim mit-pdos/etcd-grove#27, first part: retire the axioms of `etcd_robust`'s and `k8s_robust`'s trust
base about prometheus/client_golang (v1.24.1) and the metrics wrappers that need no float arithmetic.
Result: **none is retirable without a change outside the claim**; two of the wrappers' axioms were
false of Go and are restated (`notes/specs-only/ledger.md`, 2026-11-21). This re-checks prove-promdeep's
triage of 2026-11-20 (its file in `/shared/tmp` is gone; its summary is `notes/status-history.md`,
2026-11-20, "promdeep") against the current `lean`.

## Why each stays

Every client_golang constructor and the registry rest on three predicates that are themselves
trusted: `prometheus.collectorName` and `prometheus.nameFree` (axioms, `Registry.lean`; with
`prometheus.nameUnclaimed`, `Proof/runtime/Start.lean`, the trusted start model: excluded from the
claim, they change only with Upamanyu's sign-off) and `prometheus.vecLabels` (opaque, pure,
`Labels.lean`).

| axiom | Go needs floats? | blocker |
|---|---|---|
| `NewCounter`, `NewGauge`, `NewHistogram` | posts `counterSpec` (`Add`: `v < 0`, `float64(uint64(v)) == v`), `gaugeSpec` (`Add`, `Inc`, `Dec`: float add), `histSpec` (`Observe`) | floats (#654), and the post `collectorName`, an axiom: no proof can establish it until it is a definition (trusted start model) |
| `NewGaugeFunc` | no | post `collectorName` (as above) |
| `NewCounterVec`, `NewGaugeVec`, `NewHistogramVec` | `newHistogram`'s bucket order (histograms) | posts `collectorName` (as above) and `vecLabels`, opaque: to be proved it must become what it means, the vector's descriptor and its mutex-guarded `metricMap`, which a pure `Prop` cannot hold (an Iris predicate, restating it in the 13 package facts that carry it and `etc/gen-init.py`) |
| `MustRegister` | no | consumes `nameFree n` (abstract): a proof over `Registry.Register` needs `nameFree` defined over the default registry's state, and that state from prometheus's initializer (`opaqueInitsOk`/`initFuncsOk`: claim #23; its `init()` registers the process and Go collectors) |
| `Register` | no | its pre is grpc-prometheus's `promSrvMetrics` (axiom, `InvGrpcServer.lean`: claim #24), which says nothing of the collector's `Describe`; and the registry state, as `MustRegister` |
| `CounterVec.WithLabelValues` | post `counterSpec`'s `Add(float64(n))` | floats; and the pre's `vecLabels` (above) |
| `GaugeVec.WithLabelValues` | post `gaugeSpec` (float add) | floats; `vecLabels` |
| `HistogramVec.WithLabelValues` | post `observerSpec` (`Observe`) | floats; `vecLabels` |
| `GaugeVec.With` | no (`Set` is `atomic.StoreUint64(&g.valBits, math.Float64bits(val))`) | `vecLabels` only. Proving it over translated `vec.go`/`gauge.go`/`desc.go`/`labels.go` (plus client_model's `dto.LabelPair` and `internal`'s sorter) needs the vector's invariant, which only the still-trusted `NewGaugeVec` could state: the trust would move into a stronger constructor axiom, not shrink. Worth doing with `collectorName` as a definition, when the constructors become provable |
| `ExponentialBuckets` | yes (`start *= factor`, the `<= 0` checks) | floats |
| `Perennial.github_com.prometheus.client_golang.prometheus.opaqueInitsOk`/`initFuncsOk` | | claim #23 (trusted initializers) |
| `grpc_prometheus.*` (4), `promSrvMetrics`(`_persistent`) | | claim #24 (grpc) |
| `membership.setIsLearnerMetric`, `membership.RaftCluster.updateMembershipMetric`, `addFeatureGateMetrics`, `monitorFileDescriptor` | | claim #18 (etcd's own) |
| k8s etcd3 `metrics.RecordEtcdRequest`, `RecordListLatency`, `OperationLatencyTracker.Record`, `RecordStorageListMetrics` | yes (`Observe(sinceInSeconds(t))`; `Add(float64(n))`) | floats |
| k8s etcd3 `metrics.RecordEtcdEvent`, `RecordEtcdBookmark`, `NewEtcdMetricsTracker` | no (`Inc`, `WithLabelValues`) | names-only component-base `metrics`: a proof needs it translated (lazy registration, label allow-lists, `noop`), its vectors' state from the etcd3 metrics initializer (`opaqueInitsOk`, claim #23), and whether they are registered (`IsCreated`) as an invariant every caller of `Register` keeps |

## What was false (fixed)

`OperationLatencyTracker.Record` took any non-nil tracker and any error, `NewEtcdMetricsTracker` any
labels; Go panics on a zero tracker, on a typed-nil `*status.Error`, and (registered) on a non-UTF-8
label: `examples/premisefix/latencytracker`, the ledger's entry of 2026-11-21. Restated with
`metrics.latencyTrackerOk` (opaque, `Proof/k8s_io/apiserver/pkg/storage/etcd3/metrics/Tracker.lean`),
`statusErrOk` and `utf8Valid`. The other prometheus specs were re-read against v1.24.1 and hold.

## What would unblock the rest

1. Perennial#654 (IEEE floats): `counterSpec`, `gaugeSpec`, `histSpec`/`observerSpec`,
   `ExponentialBuckets`, `newHistogram`'s checks, the recorders' `Observe`/`Add`.
2. `collectorName` and `nameFree` as definitions over a model of the default registry (descriptors
   registered, by name and ID), with program start handing out its unregistered part: a change to
   the trusted start model (Upamanyu's sign-off), with prometheus's initializer proved (#23).
3. Then `vecLabels` as an Iris predicate (the vector's invariant), and client_golang's `desc.go`,
   `vec.go`, `counter.go`, `gauge.go`, `value.go`, `labels.go`, `registry.go` translated
   (`Code/github_com/prometheus/client_golang/prometheus.toml`, now names-only).
