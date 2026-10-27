---
upstream: unchecked
checked: 2026-10-27
links:
  - issues/nonissues/etcd-featuregate-enabled-panic-undocumented.md: related, different (`Enabled` on an unregistered feature)
---

> Filed directly in `issues/nonissues/` (2026-10-27): a documentation finding, parked like its sibling
> `etcd-featuregate-enabled-panic-undocumented`; unreachable through `embed`.

# etcdserver: `NewServer` panics unless `ServerConfig.ServerFeatureGate` is a `MutableFeatureGate`; the config does not say so

- **Status**: an unstated precondition (documentation). `ServerConfig.ServerFeatureGate` is declared
  as the read-only interface `featuregate.FeatureGate`, but `NewServer` type-asserts it to
  `featuregate.MutableFeatureGate`.
- **Where**: the fork `upamanyus/etcd` at `etc/goose.py`'s etcd pin. `config.ServerConfig.ServerFeatureGate
  featuregate.FeatureGate` (`server/config/config.go:198-199`, "ServerFeatureGate is a server level
  feature gate"); `NewServer` calls `addFeatureGateMetrics(cfg.ServerFeatureGate, …)`
  (`server/etcdserver/server.go:338`), which does `fg.(featuregate.MutableFeatureGate).GetAll()`
  (`server/etcdserver/server.go:2462`), a single-value assertion that panics on failure.
- **What happens**: `NewServer` with a `ServerConfig` whose `ServerFeatureGate` implements
  `FeatureGate` but not `MutableFeatureGate` (e.g. a read-only wrapper) panics with `interface
  conversion`. `embed` always passes `features.NewDefaultServerFeatureGate(...)`
  (`server/embed/config.go:581`, `embed/etcd.go:238`), which is mutable, so etcd's own entry point does
  not reach it; a program building a `ServerConfig` itself, as the interface type invites, can.
- **Expected**: the field's comment states that the gate must be a `MutableFeatureGate`, or the field
  has that type, or `addFeatureGateMetrics` uses the two-value assertion and skips the metrics.
- **How the proof handles it**: `NewServer.spec` takes as a premise that the gate is a
  `*featuregate.featureGate` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean:162-163`, and
  `:310-311` for `specM`).
- **Possible fixes**: document the requirement on `ServerConfig.ServerFeatureGate`; or declare it
  `featuregate.MutableFeatureGate`; or `if mfg, ok := fg.(featuregate.MutableFeatureGate); ok { … }`.
- **Found**: 2026-10-27, by the `NewServer` candidate spec (an implementation-independent restatement
  of `NewServer.spec`, which kept the assertion as a real precondition).
