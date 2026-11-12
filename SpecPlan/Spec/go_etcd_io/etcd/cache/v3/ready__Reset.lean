/-
`ready.Reset` (`cache/*.go`), an internal helper.
Users: `Cache.watchEvents` (an upstream error).
Proof sketch: as `Set`.
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

/-- `r.Reset()`. -/
def ready.Reset.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isReady r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.ready.ty @!! go!"Reset")) (Val #()))
  {{ RET #(); True }}

end spec

end Cache
end EtcdGrove
end Perennial
