---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# etcdserver: `NewServer` panics unless `ServerConfig.ServerFeatureGate` is a `MutableFeatureGate`; the config does not say so

`config.ServerConfig.ServerFeatureGate` is declared as the read-only interface
`featuregate.FeatureGate`, but `NewServer` (through `addFeatureGateMetrics`) asserts it to
`featuregate.MutableFeatureGate` with a single-value assertion, so a gate that is only a
`FeatureGate` panics `NewServer`.

**Why not an issue:** a precondition etcd meets: `embed` always passes
`features.NewDefaultServerFeatureGate(...)`, which is mutable; only a program building its own
`ServerConfig` with a read-only gate reaches it. Documentation only.

## Proof

no: `NewServer.spec` takes the gate to be a `*featuregate.featureGate`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean`), which `embed` meets.

## Notes

A fix: document the requirement on the field, declare it `MutableFeatureGate`, or use the
two-value assertion and skip the metrics. Upstream search 2026-11-01 (`ServerFeatureGate
MutableFeatureGate`): nothing.
