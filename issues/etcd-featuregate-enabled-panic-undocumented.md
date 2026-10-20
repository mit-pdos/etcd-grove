---
upstream: none
checked: 2026-10-20
links:
  - kubernetes/kubernetes#84865 pr merged: introduced the panic in component-base's featuregate (2019, "should not silently return false"); documented on `(*featureGate).Enabled` only, the interface comment kept, as in component-base's master today
  - etcd-io/etcd#18062 pr merged: copied component-base's featuregate into etcd's `pkg/featuregate` with the same interface comment; the panic not discussed
---

# pkg/featuregate: `FeatureGate.Enabled` panics on an unregistered feature; the interface does not say so

- **Status**: documentation. The interface's contract omits a panic its only implementation has.
  The concrete method documents the panic; the interface that callers hold does not. Not
  reachable from etcd's server, which asks only for the features it registers.
- **Where**: the fork `upamanyus/etcd` at `etc/goose.py`'s etcd pin. The interface
  `FeatureGate.Enabled(key Feature) bool` (`pkg/featuregate/feature_gate.go:87-88`) says only "Enabled
  returns true if the key is enabled". Its implementation `(*featureGate).Enabled`
  (`pkg/featuregate/feature_gate.go:333-343`) says "If the key is not known, this call will
  panic" and does panic, with `feature %q is not registered in FeatureGate %q`. The server holds the
  gate as the interface (`config.ServerConfig.ServerFeatureGate`) and calls it through
  `EtcdServer.FeatureEnabled` and directly (`server/etcdserver/server.go:351,396,1162,2276`,
  `v3_server.go:366,511,1063`, `api/v3rpc/health.go:39`).
- **What happens**: `features.NewDefaultServerFeatureGate("x", lg).Enabled("NoSuchFeature")`
  panics. Someone who reads only the interface (what `ServerConfig` exposes) cannot tell that
  `Enabled` is partial.
- **Expected**: the interface's comment states the precondition, for example "Enabled panics if
  the key is not a registered feature".
- **How the proof handles it**: the feature gate's contract `isFeatureGate`
  (`Proof/go_etcd_io/etcd/server/v3/features/Defs.lean`) holds only for `serverFeatures`, the
  keys of `DefaultEtcdServerFeatureGates`. Each call site discharges membership. Until 2026-10-18
  the contract covered every key, which no Go feature gate meets (`notes/STATUS.md`, "Item 9,
  point 7").
- **Possible fixes**: document the panic on the interface method. Alternatively, return `false`
  for an unknown key (a behavior change).
- **Found**: 2026-10-18, writing the trust-boundary spec of `features.NewDefaultServerFeatureGate`
  (item 9, point 7).
