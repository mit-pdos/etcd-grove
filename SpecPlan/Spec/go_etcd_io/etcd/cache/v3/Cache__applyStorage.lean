/-
`Cache.applyStorage` (`cache/*.go`), an internal helper.
Users: `Cache.watch`'s goroutine.
Proof sketch: a loop `select`ing on the cache's context and the store watcher's channel (`watcherConsumer`, the store's range): each response `store.Apply.spec` (its position covered: `storeUpTo`), a closed channel returns `nil`.
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

/-- `c.applyStorage(storeW)` by the store watcher's consumer: returns (an error, or `nil`). -/
def Cache.applyStorage.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (w : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ storeApplier c w }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"applyStorage")) (Val #w))
  {{ (err : GoInterface), RET #err; True }}

end spec

end Cache
end EtcdGrove
end Perennial
