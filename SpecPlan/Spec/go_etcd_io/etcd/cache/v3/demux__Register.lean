/-
`demux.Register` (`cache/*.go`), an internal helper.
Users: `Cache.Watch`, `Cache.watch` (the store watcher).
Proof sketch: under the write lock: the watcher goes active or lagging at its start (`maxRev + 1` for `0` once fed); the invariant takes the producer end at that position, the consumer end at the requested one goes to the caller (equal, or for `0` the consumer's `none`).
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

/-- `d.Register(w, startingRev)`: the consumer end of `w`, on its range (the prefix's for an unfiltered watcher), from `startingRev` (`none`: from the demux's newest revision). -/
def demux.Register.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s w : Loc) (rng : Option KeyRange) (startingRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ isWatcher w ∗ watcherNew w rng }}
    (App (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"Register")) (Val #w)) (Val #startingRev))
  {{ RET #(); watcherConsumer w γ (rng.getD (prefixRange pfx))
      (.live (if startingRev = W64 0 then none else some (sint.Z startingRev)) 0) }}

end spec

end Cache
end EtcdGrove
end Perennial
