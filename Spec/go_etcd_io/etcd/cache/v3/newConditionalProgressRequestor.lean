/-
`newConditionalProgressRequestor` (`cache/*.go`), an internal helper.
Users: `newCache` (the client's `Watcher` as the notifier).
Proof sketch: allocates the struct, its `Cond` over its mutex; allocates the invariant (`waiting`, `stopped`).
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

/-- `newConditionalProgressRequestor(notifier, clock, interval)`. -/
def newConditionalProgressRequestor.spec : Prop :=
  ∀ (n clk : GoInterface) (ri : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ progressNotifierOk n ∗ clockOk clk }}
    (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.newConditionalProgressRequestor)) (Val #n)) (Val #clk)) (Val #ri))
  {{ (p : Loc), RET #p; isProgressRequestor p }}

end spec

end Cache
end EtcdGrove
end Perennial
