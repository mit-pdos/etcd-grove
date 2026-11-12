/-
`newDemux` (`cache/*.go`), an internal helper.
Users: `NewDemux`.
Proof sketch: allocates the maps, the history ring (`newRingBuffer.spec`, batches by their first event's revision), the notifier; allocates the invariant (nothing registered, not initialized).
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

/-- `newDemux(historyWindowSize, resyncInterval)`: a demux for any cluster, prefix and store, not yet fed. -/
def newDemux.spec : Prop :=
  ∀ (γ : Cluster) (pfx : GoString) (s : Loc) (hws : w64) (ri : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ ⌜0 < sint.Z hws ∧ sint.Z hws ≤ 2 ^ 61⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.newDemux)) (Val #hws)) (Val #ri))
  {{ (d : Loc), RET #d; isDemux d γ pfx s ∗ demuxFeed d γ pfx s none }}

end spec

end Cache
end EtcdGrove
end Perennial
