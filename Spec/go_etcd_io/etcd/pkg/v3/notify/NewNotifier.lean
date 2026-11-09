/-
## `notify.NewNotifier()`

**Users.** `EtcdServer.start` (`server.go`: `leaderChanged`, `firstCommitInTerm`), the lessor's
demotion notifier. Snippet: `examples/specreq/wait/notify.go`.

**Proof sketch.** Allocates the struct and an unbuffered channel (Perennial's `chan.make`: `isChan`,
`ownChan` open), the mono-nat at `0`, the lock with its invariant.

**Changes.** The old spec (`specs-ref`'s `NewNotifier.lean`) fixed a client predicate the closes
carried; restated over the epoch counter (no client predicate: TaDa, not HoCAP).

Round 1: the count `notifyCount γ 0` handed to the caller (provability F8).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.notify.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Notify

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.notify.Assumptions]

/-- A new notifier, no notification yet. -/
def NewNotifier.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.notify.NewNotifier)) (Val #()))
  {{ (n : Loc), RET #n; ∃ γ : NotifyNames, notifierAt n γ ∗ notifyCount γ 0 ∗ notifyLb γ 0 }}

end spec
end Notify
end EtcdGrove
end Perennial
