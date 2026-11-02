---
upstream: none
checked: 2026-10-21
links:
  - kubernetes/kubernetes#84865 pr merged: introduced the panic in component-base's featuregate (2019, "should not silently return false"); documented on `(*featureGate).Enabled` only, as in component-base's master today
  - etcd-io/etcd#18062 pr merged: copied component-base's featuregate into etcd's `pkg/featuregate` with the same interface comment
blocks-proof: no
---

# pkg/featuregate: `FeatureGate.Enabled` panics on an unregistered feature; the interface does not say so

The interface method `FeatureGate.Enabled(key)` says only "Enabled returns true if the key is
enabled", while its only implementation, `(*featureGate).Enabled`, documents and does panic for a
key that is not registered. The server holds the gate as the interface.

**Why not an issue:** documentation only, and unreachable from etcd's server, which asks only for
the features it registers.

## Proof

no: the feature gate's contract (`Proof/go_etcd_io/etcd/server/v3/features/Defs.lean`) holds for
the registered server features, and each call site discharges membership, as etcd does.

## Notes

Parked 2026-10-23 (documentation, skipped for now). The fix: state the panic on the interface
method.
