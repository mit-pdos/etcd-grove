/-
`newCache` (`cache/*.go`), an internal helper.
Users: `New`.
Proof sketch: as `New.spec`'s sketch, from `CfgValid` on.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `newCache(client, prefix, cfg, clock)`: `New` after the options. -/
def newCache.spec : Prop :=
  ∀ (client : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (cfg : go_etcd_io.etcd.cache.v3.Config)
    (clk : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗ isClient client γ who ∗ etcdPeek γ ∗ clockOk clk ∗ ⌜CfgValid cfg → CfgBounded cfg⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.newCache)) (Val #client)) (Val #pfx)) (Val #cfg)) (Val #clk))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜¬ CfgValid cfg ∧ c = null ∧ err ≠ GoInterface.nil⌝ ∨
      (⌜CfgValid cfg ∧ err = GoInterface.nil⌝ ∗ isCache c γ who pfx ∗ cacheOpen c 1) }}

end spec

end Cache
end EtcdGrove
end Perennial
