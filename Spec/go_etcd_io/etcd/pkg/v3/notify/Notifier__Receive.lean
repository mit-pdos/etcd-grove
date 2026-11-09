/-
## `(*Notifier).Receive()`

**Users.** `EtcdServer.LeaderChanged`, `FirstCommitInTermNotify` (`server.go`), read by the read
loop (`read.go:98,163,195`); the lessor's and the watch server's leader monitors. Concurrent
callers. Snippet: `examples/specreq/wait/notify.go` (`ReqNotifyAfterReceive`).

**Proof sketch.** `RLock`; read `n.channel` (the lock invariant: the channel of the current epoch
`k`, the mono-nat at `k`: `notifyChan γ ch k`, `notifyLb γ k`); `RUnlock`.

**Changes.** Restated over the epoch counter (see `NewNotifier.lean`). The reader slot of `n.mu`
comes from the caller's thread token (the bounds plan: the owner's thread pool), given back.

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

/-- **The current epoch's channel**: `k` notifications had happened when it was read, so a receive
on it completes only after a later `Notify`. -/
def Notifier.Receive.spec : Prop :=
  ∀ (n : Loc) (γ : NotifyNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify ∗ notifierAt n γ ∗ threadTok }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.notify.Notifier.ty @!! go!"Receive"))
      (Val #()))
  {{ (ch : Loc), RET #ch; threadTok ∗ ∃ k, notifyChan γ ch k ∗ notifyLb γ k }}

end spec
end Notify
end EtcdGrove
end Perennial
