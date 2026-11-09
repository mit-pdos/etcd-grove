/-
# The server's feature gate (`server/features`): vocabulary (batch 2e)

etcd's server reads its features through `cfg.ServerFeatureGate` (a `featuregate.FeatureGate`
interface): `NewServer` asks `LeaseCheckpointPersist`, `LeaseCheckpoint`; the request path
`PriorityRequest`, `TxnModeWriteWithSharedBuffer`, `FastLeaseKeepAlive`; the backend
`NonBlockingDefrag`; v3rpc `StopGRPCServiceOnDefrag`; and `addFeatureGateMetrics` type-asserts it to
`*featuregate.featureGate` (a panic for any other dynamic type).

* `serverGate fg` (persistent): **`fg` is a `*featuregate.featureGate` in which every feature of
  `server/features`' `DefaultEtcdServerFeatureGates` is registered**, so that `Enabled(f)` of a
  registered feature returns its value (some `bool`) without a panic (`featuregate.go`: `Enabled`
  panics on an unregistered feature: the axiom sweep's k8s finding has the same shape). Intended
  realization: `pkg/v3/featuregate`'s trusted contract of the gate (its maps read under its lock),
  with the server's features in its known set. Produced by `NewDefaultServerFeatureGate`.
* `enabled fg f` (persistent): `Enabled(f)` has some fixed answer: none of this repository's specs
  depend on the answer, so it is not named.

## Laws

`serverGate_persistent`, `serverGate_ptr` (the dynamic type `addFeatureGateMetrics` asserts).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.features
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.features

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Features

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **`fg` is etcd server's feature gate** (persistent; see the header). -/
opaque serverGate (fg : GoInterface) : IProp GF := iprop(True)

def serverGate_persistent.spec : Prop := ∀ fg, Persistent (serverGate (GF := GF) fg)

/-- The gate is a non-nil `*featuregate.featureGate`. -/
def serverGate_ptr.spec : Prop := ∀ fg, serverGate (GF := GF) fg ⊢
  ⌜∃ p : Loc, p ≠ null ∧
    fg = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p⌝

end res

end Features
end EtcdGrove
end Perennial
