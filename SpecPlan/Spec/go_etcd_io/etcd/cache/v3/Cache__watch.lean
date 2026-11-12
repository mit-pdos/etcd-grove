/-
`Cache.watch` (`cache/*.go`), an internal helper.
Users: `Cache.getWatch`.
Proof sketch: `demux.Init.spec` at `rev` (the feed's position); a loop: `newWatcher.spec` (no filter), `demux.Register.spec` at `rev` (`storeUpTo s rev` from the restore: the applier's first response continues it), the applier's goroutine (`Cache.applyStorage.spec`, `wgAddOk`), `Cache.watchEvents.spec`, `demux.Unregister.spec`.
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

/-- `c.watch(rev)` by the loop restored at `rev - 1`: always an error, the loop's role back. -/
def Cache.watch.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (r : Nat) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheLoopAt c r ∗ ⌜sint.Z rev = r + 1⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"watch")) (Val #rev))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ cacheLoop c }}

end spec

end Cache
end EtcdGrove
end Perennial
