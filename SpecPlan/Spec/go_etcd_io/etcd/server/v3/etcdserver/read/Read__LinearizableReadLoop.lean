/-
## `(*Read).LinearizableReadLoop()`

**Users.** `EtcdServer.start` (`server.go`: `s.GoAttach(s.read.LinearizableReadLoop)`, the loop's
goroutine, once per run). Snippet: `examples/specreq/etcdserverreq/read.go` (the loop runs behind
every `ReqReadAfterWrite`).

**Proof sketch.** Each iteration: `LeaderChanged()` (`recvAny`), the `select` on it, `waitC`,
`Stopping()` (return); `EnsureTrace` (4b's traceutil); `newNotifier()`; the write `Lock`, swap
(freezing the old round's set of bounds; the new round's set empty), `Unlock`;
`requestCurrentIndex(lc)` with the old round's longest bound `l_need` (`committedLb_agree`: they
are comparable); on an error, `isStopped` (return) or `nr.notify(err)` (the round's waiters get a
`readErr`); on `(i, nil)`, `AppliedIndex()` (`A a`) and, if `a < i`, `ApplyWait(i)` (`A i`) or
`Stopping()` (return); `A i` gives `committedLb rγ l` with `i ≤ l.length` (`readEnv`), so
`Raft.readState_fire` (the round's context's `readLbQ l_need`) gives `l'` of length `i` with
`opsOf l_need <+: opsOf l'`, and `A l'.length` by downward closure; `nr.notify(nil)` with that.
On return (stopping), the pending round is not closed: its waiters leave by their contexts or
`Done()`.

**Changes.** The old spec took the read loop's precondition bundle (`isReadLoopPre` over the
server's and raft's contracts, the logger's resource, the id budget `□ |==> NR`); restated: the
environment is `readEnv`, given once to `readNew_init`, which hands out this token.

**Margin.** The loop's liveness (it serves every round while raft has a leader) is not stated.

Changes: verify-round: takes and gives back the goroutine's `threadTok` (`GoAttach` gives it one; its environment's `Logger`, `LeaderChanged`, `FirstCommitInTermNotify` take a read lock: A7-provability F6).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- **The read loop** (its goroutine): returns once the server stops; its effect is
`LinearizableReadNotify.spec`'s guarantee. -/
def Read.LinearizableReadLoop.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗ readLoopTok r ∗ threadTok }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
      go!"LinearizableReadLoop")) (Val #()))
  {{ RET #(); threadTok }}

end spec
end Read
end EtcdGrove
end Perennial
