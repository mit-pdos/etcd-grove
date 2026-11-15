/-
`newReady` (`cache/*.go`), an internal helper.
Users: `newCache`.
Proof sketch: allocates the struct and its channel; allocates `isReady`'s invariant.
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

/-- `newReady()`: a not-ready flag. -/
def newReady.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.newReady)) (Val #()))
  {{ (r : Loc), RET #r; isReady r }}

end spec

end Cache
end EtcdGrove
end Perennial
