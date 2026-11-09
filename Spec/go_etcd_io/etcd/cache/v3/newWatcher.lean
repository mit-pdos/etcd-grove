/-
`newWatcher` (`cache/*.go`), an internal helper.
Users: `Cache.Watch` (filter `KeyPredForRange`), `Cache.watch` (the store watcher, `nil`).
Proof sketch: `make(chan, bufSize)` (Perennial's channel, defined below `2^32`; a negative size panics), the struct.
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

/-- `newWatcher(bufSize, pred)`: a new watcher filtering by `rng` (`none` for a `nil` predicate). -/
def newWatcher.spec : Prop :=
  ∀ (bufSize : w64) (f : GoFunc) (rng : Option KeyRange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ ⌜0 ≤ sint.Z bufSize ∧ sint.Z bufSize < 2 ^ 32⌝ ∗ (match rng with | none => ⌜f = func.nil⌝ | some r => keyPredAt f (KeyRange.mem r)) }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.newWatcher)) (Val #bufSize)) (Val #f))
  {{ (w : Loc), RET #w; isWatcher w ∗ watcherNew w rng }}

end spec

end Cache
end EtcdGrove
end Perennial
