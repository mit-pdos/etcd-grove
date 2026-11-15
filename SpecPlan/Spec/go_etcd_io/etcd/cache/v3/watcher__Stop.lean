/-
`watcher.Stop` (`cache/*.go`), an internal helper.
Users: `demux.Unregister`, `demux.purge`.
Proof sketch: under `stopOnce`: closes the channel once (a second call does nothing); the producer end, if still held, is given up.
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

/-- `w.Stop()`: by the producer, or after it stopped. -/
def watcher.Stop.spec : Prop :=
  ∀ (w : Loc) (γ : Cluster) (rng : KeyRange) (pos : Option Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isWatcher w ∗ (watcherProducer w γ rng pos ∨ watcherStopped w) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.watcher.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); watcherStopped w }}

end spec

end Cache
end EtcdGrove
end Perennial
