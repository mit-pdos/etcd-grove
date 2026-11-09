/-
## `NewDefaultServerFeatureGate(name, lg)` (`etcd_features.go`): trusted (names only)

**Users.** `examples/lib/etcdstart`'s `newServerMode` (`ServerFeatureGate:`), etcd's `embed`
configuration. Snippet: `etcdserverboot/config.go`.

**Why it is true of Go.** `featuregate.New(name, lg)` (a `*featureGate`), then
`Add(DefaultEtcdServerFeatureGates)` (panics only on a feature registered twice with different
specs: not the case for the package's own map), so every server feature is known.

**Changes**: from `specs-ref`'s `NewDefaultServerFeatureGate.lean` (a `*featureGate` interface
value): `Features.serverGate`. **Margin.** The features' values are not stated (defaults).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.features.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Features

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.features.Assumptions]

/-- **A feature gate with the server's features registered.** -/
def NewDefaultServerFeatureGate.spec : Prop :=
  ∀ (name : GoString) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate)) (Val #name)) (Val #lg))
  {{ (fg : GoInterface), RET #fg; Features.serverGate fg }}

end spec

end Features
end EtcdGrove
end Perennial
