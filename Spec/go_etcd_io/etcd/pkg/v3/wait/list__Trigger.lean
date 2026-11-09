/-
## `(*list).Trigger(id, x)`

**Users.** The apply thread (`applyEntryNormal`, `server.go`: every applied entry's id with its
`*apply.Result`; `applyConfChange`'s), the requester's give-up (`v3_server.go:1117,1129`:
`s.w.Trigger(id, nil)` after a failed proposal or a timeout). Concurrent callers; the two may race
on one id (whichever finds the entry sends; the other finds nothing). Snippet:
`examples/specreq/wait/wait.go` (`ReqRegisterTrigger`, `ReqGiveUp`).

**Proof sketch.** The shard's `Lock`; look up and delete `id` (its registration moves out of the
invariant: the channel's send half and the saved `P id`); `Unlock`; if a channel was found, send
`x` (buffer 1, empty: never blocks) with `P id x` (the deliverer's) or nothing (the receiver's own
give-up: its receive half is consumed, so no one receives), then `close` (the one close: the entry
was deleted under the lock). If none was found, `P id x` is dropped.

**Changes.** The old spec's three cases (a gone registration, a handoff consumer, `waitTrig`) are
two: the answer's `P id x`, or the receiver's own `waitRecv` for a give-up.

**Margin.** `P id x` is lost when `id` is not registered (the requester gave up first): the caller
learns nothing of whether it was delivered.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **Delivers `x` to `id`'s receiver, if registered** (with `P id x`), or gives up the caller's own
registration (its `waitRecv`). Never blocks, never panics. -/
def list.Trigger.spec : Prop :=
  ∀ (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF) (id : w64) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ listAt l γw P ∗
      (P id x ∨ ∃ ch, waitRecv γw id ch) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty @!! go!"Trigger"))
      (Val #id)) (Val #x))
  {{ RET #(); True }}

end spec
end Wait
end EtcdGrove
end Perennial
