/-
`watcher.Compact` (`cache/*.go`), an internal helper.
Users: `demux.resyncLaggingWatchers` (a watcher behind the history's start).
Proof sketch: under `stopOnce`: sets `cancelResp` (a compaction's cancel) and closes the channel.
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

/-- `w.Compact(rev)`: the watcher stopped with a compaction's cancel pending for its consumer. -/
def watcher.Compact.spec : Prop :=
  ∀ (w : Loc) (γ : Cluster) (rng : KeyRange) (pos : Option Int) (compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isWatcher w ∗ watcherProducer w γ rng pos }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.watcher.ty @!! go!"Compact")) (Val #compactRev))
  {{ RET #(); watcherStopped w }}

end spec

end Cache
end EtcdGrove
end Perennial
