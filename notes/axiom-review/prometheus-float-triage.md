# The float-dependent metrics axioms after IEEE 754 floats (claim #27, float part, prove-metrics-float, 2026-11-22)

Claim mit-pdos/etcd-grove#27, second part: retire the float-dependent axioms deferred by the first part
(`prometheus-nonfloat-triage.md`), now that the pin (`d845edaf90`) has Perennial `c14cca87a` (#654): each
float operation steps relationally (`wp_float64_<op>`), exact rational arithmetic rounded to nearest even,
any NaN for a NaN result; a float-to-integer conversion is some integer.

Result: **one axiom retired** (`rate.Limiter.Reserve`), none added; **no spec found false** (each re-read
against the Go code, NaN, infinities, signed zeros and overflow included).

## Retired

- `rate.Limiter.Reserve` (x/time/rate v0.16.0): `Reserve`, `ReserveN`, `reserveN`, `advance`,
  `tokensFromDuration`, `durationFromTokens` translated (`Code/golang_org/x/time/rate.toml`).
  `reserveN` has its own spec (`Spec/golang_org/x/time/rate/Limiter__reserveN.lean`: a reservation whose
  `lim` is the limiter, for any time, count and maximum wait), proved for any limiter state: the proof
  needs no fact about float values (every operation steps, comparisons are total, `time.Duration(f)` of an
  out-of-range or NaN `f` is some duration, as Go's spec leaves it to the implementation without a
  panic). `advance`, `tokensFromDuration` and `durationFromTokens` are private lemmas of its proof file.
  Two local workarounds, both proofs: `haveI : go.NotInterface go.float64` (`Limit`'s value methods,
  `perennial-changes.md`, "`go.NotInterface` of the predeclared named types"), and a `rw [method_unfold
  (t := ...) (m := ...)]` in place of `wp_method_call`, which rewrites the first `methods` of the goal
  (the deferred `Unlock` in the `defer` cell) rather than the call in evaluation position.

## Not retired

| axiom | why |
|---|---|
| `prometheus.ExponentialBuckets` | **Retired 2026-11-23** (small-leaves-2, claim #35): translated and proved, the doubling law proved locally from Perennial's definitions (`perennial-changes.md`). Before: its body steps (only `panic`, `make` and `start *= factor`), but its spec's exact buckets need the doubling law (`float64Mul x 2.0` of a normal `x` with a normal result is `x + 2^52`): a theorem of Perennial's model, about Perennial's own definitions (`floorLog2`, `roundHalfEven`, `encode`), which goes to Perennial's `Theory/Float.lean` (CLAUDE.md, no `Proof/Lib/`). A Perennial change: recorded in `perennial-changes.md` (2026-11-22), not made. Spec re-read: true. |
| `math.Ceil` (also #26) | Perennial translates only `math`'s tables: `Ceil` is names-only, and on amd64 it is `archCeil`, assembly, behind the opaque `haveArchCeil`. A Perennial change (translate `ceil`/`floor`/`Modf`, model `archCeil`): recorded, not made. Spec (some `float64`) true. |
| `rate.Limiter.Wait` | No longer float-blocked (its bucket is `reserveN`, now proved). Left: `wait`'s `fmt.Errorf` (rate would import `fmt`, a package-init change), the non-blocking and blocking `select`s on `ctx.Done()` and the timer, the timer closure, and `Reservation.CancelAt` (float arithmetic, which steps, plus the limiter's mutex reached through the reservation). Ordinary proof work, out of this pass. |
| `CounterVec`/`GaugeVec`/`HistogramVec.WithLabelValues` | Their results' `counterSpec`/`gaugeSpec`/`observerSpec` would hold over the IEEE model (`counter.Add`'s `v < 0` check is `lt_zero_false_of_sign_clear`), but `prometheus` is names-only: a proof needs `vec.go`, `counter.go`, `gauge.go`, `value.go`, `labels.go` translated and the vector's invariant, which only the trusted premise `vecLabels` (opaque) and the constructors' `collectorName` posts state. Trusted premises: not changed. |
| `NewCounter`, `NewGauge`, `NewHistogram`, `NewCounterVec`, `NewGaugeVec`, `NewHistogramVec` (their float results) | Each posts `collectorName` (an axiom of the trusted start model) and, for the vectors, `vecLabels`: no proof can establish them while they are trusted premises. |
| k8s etcd3 `metrics.RecordEtcdRequest`, `RecordListLatency`, `RecordStorageListMetrics`, `OperationLatencyTracker.Record` | The float part (`Observe(sinceInSeconds(t))`, `Add(float64(n))`) would step; but the package is names-only, its vectors are component-base `metrics` (names-only: lazy registration, label allow-lists) held in package variables from the etcd3 metrics initializer (`opaqueInitsOk`, claim #23), and `errorReason` reaches grpc's `status.FromError`. |
