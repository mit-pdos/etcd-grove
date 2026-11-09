/-
## `(*Notifier).Notify()`

**Users.** The server's ready handler (`server.go`: `leaderChanged.Notify()` on a leader change,
`firstCommitInTerm.Notify()` on the first commit of a term), the lessor's demotion. Concurrent
callers (each closes the channel it swapped out, a different one). Snippet:
`examples/specreq/wait/notify.go`.

**Proof sketch.** A fresh channel (`chan.make`); `Lock`; swap (the invariant's epoch `k` to `k + 1`,
the mono-nat bumped); `Unlock`; close the old channel with its receivers' fact `notifyLb γ (k + 1)`
(the old channel's ownership was the invariant's, handed to this caller by the swap: no double
close).

**Changes.** Restated over the epoch counter; round 1: the count is the client's, moved by its
atomic update at the swap (provability F8). The membership package's notifier
(`membership/cluster.go:620`) keeps it in its own invariant.

**Margin.** None: the notification is counted when the channel is swapped, before it is closed.
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

/-- **A notification**: the caller's update moves the count at the swap (`k` to `k + 1`), the
current channel is then closed. -/
def Notifier.Notify.spec : Prop :=
  ∀ (n : Loc) (γ : NotifyNames) (Q : Nat → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify ∗ notifierAt n γ ∗
      AU <{ ∃∃ (k : Nat), notifyCount γ k }> @ ⊤ \ ↑notifyN, ∅
        <{ notifyCount γ (k + 1), COMM Q k }> }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.notify.Notifier.ty @!! go!"Notify"))
      (Val #()))
  {{ RET #(); ∃ k, Q k ∗ notifyLb γ (k + 1) }}

end spec
end Notify
end EtcdGrove
end Perennial
