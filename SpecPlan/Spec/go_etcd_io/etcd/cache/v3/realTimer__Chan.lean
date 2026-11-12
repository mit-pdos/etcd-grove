/-
`realTimer.Chan` (`cache/*.go`), an internal helper.
Users: `Cache.Watch`'s goroutine, `conditionalProgressRequestor.run` (via `timerOk`).
Proof sketch: loads `r.timer.C` (Perennial's `time.Timer`).
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

/-- `r.Chan()`: the timer's channel. -/
def realTimer.Chan.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ realTimerAt r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.realTimer.ty @!! go!"Chan")) (Val #()))
  {{ (ch : Loc), RET #ch; realTimerAt r ∗ timerChan ch }}

end spec

end Cache
end EtcdGrove
end Perennial
