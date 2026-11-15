/-
`Cache.getWatch` (`cache/*.go`), an internal helper.
Users: `Cache.getWatchLoop`.
Proof sketch: `Cache.get.spec` on the cache's context (`ctxPrin_child` of `Background`), then `Cache.watch.spec` from the response's revision plus one.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `c.getWatch()` by the watch loop: always an error (`watch` never returns `nil`). -/
def Cache.getWatch.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheLoop c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"getWatch")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ cacheLoop c }}

end spec

end Cache
end EtcdGrove
end Perennial
