/-
`demux.BroadcastProgressTo` (`cache/*.go`), an internal helper.
Users: `Cache.Watch`'s goroutine (`WithProgressNotify`'s timer).
Proof sketch: as `BroadcastProgress`, for one active watcher, under the read lock (the producer's send is non-blocking).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: two `BroadcastProgressTo`s run at once under the read lock and both enqueue to the same watcher: the producer end is shared among read-lock holders for progress sends only (each a notification at `maxRev`, quiet under the read lock); the realization splits it so.
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

/-- `d.BroadcastProgressTo(w)`. -/
def demux.BroadcastProgressTo.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s w : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ isWatcher w ∗ threadTok }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"BroadcastProgressTo")) (Val #w))
  {{ RET #(); threadTok }}

end spec

end Cache
end EtcdGrove
end Perennial
