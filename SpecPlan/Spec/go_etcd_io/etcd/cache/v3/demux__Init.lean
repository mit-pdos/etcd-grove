/-
`demux.Init` (`cache/*.go`), an internal helper.
Users: `Cache.watch` (before the upstream watch from `minRev`).
Proof sketch: under the write lock: nothing for `0`; a first initialization; a continuation (`minRev = maxRev + 1`: the feed's position already `minRev`); otherwise `purge` (every watcher stopped: their consumers see the channel closed) and `minRev` set.
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

/-- `d.Init(minRev)` by the feeder: the upstream watch's position becomes `minRev` (unchanged for `0`). -/
def demux.Init.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (pos : Option Int) (minRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ demuxFeed d γ pfx s pos }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"Init")) (Val #minRev))
  {{ RET #(); demuxFeed d γ pfx s (if minRev = W64 0 then pos else some (sint.Z minRev)) }}

end spec

end Cache
end EtcdGrove
end Perennial
