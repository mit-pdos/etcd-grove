/-
`watcher.enqueueResponse` (`cache/*.go`), an internal helper.
Users: the demux's broadcasts and resync (under its lock).
Proof sketch: filters the events by the predicate (`keyPredAt`); a response left empty is reported delivered; a non-blocking send on the channel (open: the producer end is held).
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

/-- `w.enqueueResponse(resp)` by the producer end, for a response certified from its position (on a range containing the watcher's): `true` and the position moved (sent, or filtered to nothing), or `false` (the buffer full) and nothing sent. -/
def watcher.enqueueResponse.spec : Prop :=
  ∀ (w : Loc) (γ : Cluster) (rng rng0 : KeyRange) (pos pos' : Option Int)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isWatcher w ∗ watcherProducer w γ rng pos ∗ watchRespAt resp m ∗ respFact γ rng0 pos m pos' ∗ ⌜∀ k, KeyRange.mem rng k → KeyRange.mem rng0 k⌝ }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.watcher.ty @!! go!"enqueueResponse")) (Val #resp))
  {{ (ok : Bool), RET #ok;
      if ok then watcherProducer w γ rng pos' else watcherProducer w γ rng pos }}

end spec

end Cache
end EtcdGrove
end Perennial
