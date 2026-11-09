/-
# `pkg/notify`: a broadcast notifier (batch 2c), vocabulary

A `Notifier` holds one channel; `Receive()` returns the current one, `Notify()` swaps in a fresh
channel and closes the old one (`notify.go`). Each channel is closed once (the swap happens under the
lock, before the close), so a receive on a channel returned by `Receive` completes exactly when a
`Notify` after that `Receive` has run. Users: the server's `leaderChanged` and `firstCommitInTerm`
notifiers (`server.go`), received by the read loop (`read.Read.LinearizableReadLoop`,
`requestCurrentIndex`: a leader change ends a read-index round with `ErrLeaderChanged`, a first
commit in a term resends the read index), the lessor's and the watch's leader monitors.

## Vocabulary

* `NotifyNames` (opaque ghost names).
* `notifierAt n γ` (persistent): `n` is a notifier with ghost names `γ`.
* `notifyLb γ k` (persistent): at least `k` notifications have happened.
* `notifyCount γ k` (exclusive, the client's): exactly `k` notifications have happened. `Notify`
  moves it by an atomic update the caller supplies (at the swap), so a client can tie its own state
  to the count (`ReqNotifyAfterReceive`); one that does not care keeps it in an invariant. Laws:
  `notifyCount_lb`, `notifyLb_count`.
* `notifyN`: the notifier's invariants' namespace.
* `notifyChan γ ch k` (persistent): `ch` is the channel `Receive` returned after exactly `k`
  notifications; receiving on it completes only once the `k + 1`-th has happened (`notifyChan_recv`).

None of the users relies on more than "the receive completes only after a later `Notify`" for safety
(the read loop's reactions are error returns and retries); the counter is what makes that fact
statable and chainable.

## Intended realization

A ghost mono-nat of the notifications (`notifyLb` its fragment); the lock invariant holds the
current channel `c`, the epoch `k`, the authority, and Perennial's channel ownership of `c` in state
open; `notifyChan γ ch k` is `isChan ch` with a saved fact that `ch` was the channel of epoch `k`, and
the channel's close is done with the mono-nat at `k + 1` (a closed channel's receivers learn it).

## Requirement snippets

`examples/specreq/wait/notify.go` (`ReqNotifyAfterReceive`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.notify
public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.notify
public import Perennial.Proof.context

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Notify

open Iris Iris.BI

/-- A notifier's ghost names (opaque). -/
opaque NotifyNames : Type := Unit

/-- The notifiers' invariants' namespace. -/
def notifyN : Namespace := nroot .@ "notify"

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `n` is a notifier with ghost names `γ`. Persistent. -/
opaque notifierAt (n : Loc) (γ : NotifyNames) : IProp GF := iprop(True)

/-- At least `k` notifications have happened. Persistent. -/
opaque notifyLb (γ : NotifyNames) (k : Nat) : IProp GF := iprop(True)

/-- **Exactly `k` notifications have happened** (exclusive, the client's). -/
opaque notifyCount (γ : NotifyNames) (k : Nat) : IProp GF := iprop(True)

/-- `ch` is the channel of epoch `k` (returned by `Receive` after exactly `k` notifications).
Persistent. -/
opaque notifyChan (γ : NotifyNames) (ch : Loc) (k : Nat) : IProp GF := iprop(True)

def notifierAt_persistent.spec : Prop := ∀ n γ, Persistent (notifierAt (GF := GF) n γ)
def notifyLb_persistent.spec : Prop := ∀ γ k, Persistent (notifyLb (GF := GF) γ k)
def notifyChan_persistent.spec : Prop := ∀ γ ch k, Persistent (notifyChan (GF := GF) γ ch k)

def notifyCount_timeless.spec : Prop := ∀ γ k, Timeless (notifyCount (GF := GF) γ k)

def notifyCount_lb.spec : Prop := ∀ γ k, notifyCount (GF := GF) γ k ⊢ notifyCount γ k ∗ notifyLb γ k

def notifyLb_count.spec : Prop := ∀ γ (j k : Nat), notifyCount (GF := GF) γ k ∗ notifyLb γ j ⊢ ⌜j ≤ k⌝

def notifyLb_mono.spec : Prop := ∀ γ (k k' : Nat), k' ≤ k → notifyLb (GF := GF) γ k ⊢ notifyLb γ k'

/-- **Receiving on an epoch's channel** (a blocking receive or a `select` case: Perennial's
`recvAu`) completes only once the next notification has happened. -/
def notifyChan_recv.spec : Prop := ∀ (γ : NotifyNames) (ch : Loc) (k : Nat),
  notifyChan (GF := GF) γ ch k ⊢
    ∃ γc : ChanNames, isChan ch γc Unit ∗
      □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, notifyLb γ (k + 1) -∗ Φ v ok) -∗ recvAu γc Unit Φ

end vocab

end Notify
end EtcdGrove
end Perennial
