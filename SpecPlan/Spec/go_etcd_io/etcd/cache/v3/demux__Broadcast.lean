/-
`demux.Broadcast` (`cache/*.go`), an internal helper.
Users: `Cache.watchEvents` (each upstream response).
Proof sketch: under the write lock: `not initialized` and `validateRevisions.spec`'s errors leave everything; else `demux.updateStoreLocked.spec` (the history and `maxRev`) and `demux.broadcastLocked.spec` (each active watcher enqueued from its position, `watcher.enqueueResponse.spec`, a full one moved to lagging). The store's ceiling covers the response (`storeCeilLb`), so the store watcher's responses carry it.
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

/-- `d.Broadcast(resp)` by the feeder, for an upstream response certified from the feed's position: `nil` and the position moved, or an error and nothing changed. -/
def demux.Broadcast.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (pos pos' : Option Int) (r : Nat)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ demuxFeed d γ pfx s pos ∗ watchRespAt resp m ∗ respFact γ (prefixRange pfx) pos m pos' ∗ storeCeilLb s r ∗ ⌜m.hdrRev ≤ r ∧ ∀ e ∈ m.events, e.rev ≤ r⌝ }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"Broadcast")) (Val #resp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ demuxFeed d γ pfx s pos') ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ demuxFeed d γ pfx s pos) }}

end spec

end Cache
end EtcdGrove
end Perennial
