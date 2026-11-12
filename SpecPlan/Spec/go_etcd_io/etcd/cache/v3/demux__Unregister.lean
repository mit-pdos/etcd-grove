/-
`demux.Unregister` (`cache/*.go`), an internal helper.
Users: `Cache.Watch`'s goroutine, `Cache.watch`.
Proof sketch: under the write lock: deletes from both maps (the invariant gives back the producer end, if it still holds it); then `watcher.Stop.spec`.
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

/-- `d.Unregister(w)`. -/
def demux.Unregister.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s w : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ isWatcher w }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"Unregister")) (Val #w))
  {{ RET #(); watcherStopped w }}

end spec

end Cache
end EtcdGrove
end Perennial
