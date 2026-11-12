/-
`defaultConfig` (`cache/*.go`).
Users: `New` (`cfg := defaultConfig()`), `getWatchLoop` (its initial backoff).
Proof sketch: returns the composite literal; Goose's struct value is `defaultConfigM`.
Changes: unchanged (the value renamed `defaultConfigM`).
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `defaultConfig()`: the default configuration. -/
def defaultConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.defaultConfig)) (Val #()))
  {{ RET #defaultConfigM; True }}

end spec

end Cache
end EtcdGrove
end Perennial
