/-
`kvItemLess` (`cache/*.go`), an internal helper.
Users: the store's B-tree (its `less`).
Proof sketch: reads both items' immutable keys; Go's string `<` is `GoStringLt`.
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

/-- `kvItemLess(a, b)`: `a.key < b.key`. -/
def kvItemLess.spec : Prop :=
  ∀ (a b : Loc) (ka kb : GoString) (kva kvb : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ kvItemAt a ka kva ∗ kvItemAt b kb kvb }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.kvItemLess)) (Val #a)) (Val #b))
  {{ RET #(decide (EtcdModel.keyLt ka kb)); True }}

end spec

end Cache
end EtcdGrove
end Perennial
