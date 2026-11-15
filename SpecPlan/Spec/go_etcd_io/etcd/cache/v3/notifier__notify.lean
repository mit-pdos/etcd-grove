/-
`notifier.notify` (`cache/*.go`), an internal helper.
Users: `demux.resyncLoop`.
Proof sketch: under the write lock: replaces the channel and closes the old one (owned by the invariant: closed once).
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

/-- `n.notify()`. -/
def notifier.notify.spec : Prop :=
  ∀ (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isNotifier n }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.notifier.ty @!! go!"notify")) (Val #()))
  {{ RET #(); True }}

end spec

end Cache
end EtcdGrove
end Perennial
