---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# k8s apiserver storage metrics: recording a negative count or a non-UTF-8 label panics once the metrics are registered

Once `storage/metrics.Register()` and `storage/etcd3/metrics.Register()` have run (the apiserver
runs both, `k8s.io/apiserver/pkg/server/routes/metrics.go:53-60`), the recorders panic on inputs
their signatures accept: `RecordStorageListMetrics(gr, index, numFetched, numEvald, numReturned)`
panics with `counter cannot decrease in value` when a count is negative
(`storage/metrics/metrics.go:79-84`, `Counter.Add(float64(n))`), and it, `RecordListLatency`,
`RecordEtcdRequest` and `RecordDecodeError` panic with `label value "\xff" is not valid UTF-8` when
a label (the verb, the group, the resource or the index name) is not valid UTF-8 (prometheus'
`WithLabelValues`). Before registration every call is a no-op (component-base's `WithLabelValues`
returns `noop` while the vector is not created, `component-base/metrics/counter.go:198-201`).
`TestMetricsRegistered` in `examples/k8s7e2attack/attack_test.go` shows each panic at apiserver
`9c4ec15b8038`, component-base `cd2c1afd246a`, go1.27.3.

**Why not an issue:** a precondition the apiserver meets. The etcd3 store passes counts that are
sums of slice lengths (non-negative), literal verbs and index names, and its configured
`GroupResource`, whose group and resource are API names (DNS-label-like, ASCII). Found while
attacking the trusted statements of k8s etcd3 stage 7e-2 (`notes/k8s-7e-2-attack.md`, T16-T17,
R1). Upstream not searched.

## Proof

no: the specs take the precondition as premises (non-negative counts, `utf8Valid` labels), met by
the store (`isStore` carries `utf8Valid` of its `groupResource`). It is also a repair of this
repository's trust base: the axioms of `RecordEtcdRequest` and `RecordDecodeError` had no such
premise and were false of a registered apiserver (`notes/k8s-7e-2-attack.md`, R1).
