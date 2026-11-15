/-
**TRUST BOUNDARY, local, delete when `notes/perennial-changes.md`'s "The context model over an error
predicate" lands**: `context.WithTimeout` over a stream handler's weak context (k8s 7f-4, Addendum
T-j; option (c) of etcd-grove-81's decision of 2026-11-13, the texts of Addendum T-h2 with T-h5's
option (A)). Perennial's `context.WithTimeout.spec` takes `isContext parent`, whose `Err()` returns
only context errors; etcd's require-leader wrapper (`*cancellableContext`) returns
`rpctypes.ErrGRPCNoLeader` once cancelled, and `EtcdServer.LeaseRenew` calls
`context.WithTimeout(ctx, ...)` on such a context (through `Tracer.Start`'s `WithValue`). The general
fix is Perennial's `*cancelCtx` model over an error predicate (a parameter in place of `isCtxErr`);
until it lands, this axiom states the one instance `LeaseRenew` needs. Lean-first.
-/
module

public import Perennial.Spec.context.WithTimeout
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section axiom_
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- (TRUSTED, local; k8s 7f-4, Addendum T-j) **`context.WithTimeout(parent, timeout)` over a weak
context** `parent` (`srvCtxWeak parent pd`), the caller lending `levelTok v3rpc.ctxErrLvl` (returned):
a new context `ctx'` with a cancel function that may be called any number of times, and of `ctx'`
`v3rpc.ctxChildErr` (Perennial's `isContext` clauses of the `*timerCtx` it is, with its `Err()`
returning `nil`, a context error or etcd's no-leader error, and the `*cancelCtx` it embeds stated as
`context.madeCancelCtx`) under the descriptor `wp_WithTimeout` gives (deadline `d`, Done proposition
`True`, fresh names `γ'`), and `ctxValueFrom parent ctx'` (its `Context` field is `parent`).

Its post is Perennial's `context.WithTimeout.spec`'s (`Perennial/Spec/context/WithTimeout.lean`),
with `isContext ctx'` replaced by `ctxChildErr ctx'`, which differs from `isContext` only in its `Err`
clauses (no `□ PDone` / `isTypedErr`; the error may also be `noLeaderErr`) and in its `"#HValue"` and
`"#HParentCC"` naming `madeCancelCtx` in place of `isCancelCtx`; its premise is the same with
`isContext parent` replaced by `srvCtxWeak parent pd ∗ levelTok v3rpc.ctxErrLvl`.

**Why it is faithful** (go1.27.3 `src/context/context.go`). `WithTimeout` is
`WithDeadline(parent, time.Now().Add(timeout))`, which is `WithDeadlineCause(parent, d, nil)`: it
calls `parent.Deadline()` (`srvCtxWeak`'s `"#HDeadline"`); if the parent's deadline is earlier, it
returns `WithCancel(parent)` (a `*cancelCtx`, of the same clauses), else it allocates a `*timerCtx`
`c` and calls `c.cancelCtx.propagateCancel(parent, c)` (`:476-528`): it writes `c.Context = parent`,
calls `parent.Done()` (`"#HDone"`); if that channel is already closed, it calls
`c.cancel(false, parent.Err(), Cause(parent))` (`:485-488`): `parent.Err()` is non-nil and a context
error or `ErrGRPCNoLeader` (`"#HErrDone"`, paid with the lent token), so `cancel` does not panic on a
nil error, and `c` stores that error (`ErrGRPCNoLeader` for the wrapper: `TestWithTimeoutWeak`, which
is why `isContext ctx'` would be false, Addendum T-h1); `Cause(parent)` calls
`parent.Value(&cancelCtxKey)` (`"#HValue"`: a valid `*cancelCtx`, whose `cause` it reads under its
`mu`) or `parent.Err()` again (the token). Otherwise `parentCancelCtx(parent)` finds a valid
`*cancelCtx` `p` (`"#HParentCC"`, the Done channel known and not `closedchan`), so the `afterFuncer`
arm and the goroutine arm are not reached and `c.Context` stays `parent`; under `p.mu`, `c` is
cancelled with `p`'s stored error (a context error: `p`'s `isCancelCtx` invariant) or registered in
`p.children`, to be cancelled later with `p`'s error (a context error). Then, if `d` has not passed,
a timer is armed that cancels `c` with `DeadlineExceeded`, else `c` is cancelled with it at once.
Every error `c` stores is thus nil, a context error or the parent's `Err()` after `Done`: `c.Err()`
(no `RWMutex` reader slot, so no token: an atomic load of `c.err`, then `<-c.Done()`, which may
briefly take `c.mu` or wait for the concurrent `cancel` to close `done`) returns nil or such an error, non-nil once `c.Done()` is
closed (`cancel` stores the error before it closes the channel). The rest of `ctxChildErr` is what
Perennial proves of a `*timerCtx` (`isContext_timerCtx`): `Deadline()` returns `d`, `Done()` its
`cancelCtx`'s lazily made channel, `Value(&cancelCtxKey)` its embedded `cancelCtx`, which `context`
made (`madeCancelCtx`), as is the one `parentCancelCtx(ctx')` finds (the same one; `ctx'` is a
`*timerCtx`, not a `stopCtx`). The cancel function is `c.cancel(true, Canceled, nil)`: it cancels
`c` (a no-op once cancelled) and `removeChild(parent, c)`, which calls `parentCancelCtx(parent)` and
deletes `c` from `p.children` under `p.mu` (`parent` is not a `stopCtx`: `"#HParentCC"`).
`ctxValueFrom parent ctx'`: `c.Context` is `parent` and `context.value` walks a `*timerCtx` to it for
every key but `&cancelCtxKey`. The `WithCancel` case (parent's deadline earlier) gives a `*cancelCtx`
with the same facts (its `Deadline()` is the parent's: `d` is a binder of the post, the deadline the
child reports, as in Perennial's spec). Go evidence: `examples/premisefix/streamctx` `TestWithTimeoutWeak` (over etcd's wrapper and a
`WithValue` of it: already cancelled with `ErrGRPCNoLeader`, the child's `Err()` is it, not
`Canceled`/`DeadlineExceeded`, and `cancel()` keeps it; not yet done, the child is registered with
the wrapper's embedded `*cancelCtx`, which `parentCancelCtx` finds, so no goroutine is started, and
the wrapper's `Cancel(ErrGRPCNoLeader)` gives the child `Canceled`; its own timeout
`DeadlineExceeded`, its cancel `Canceled`; `RenewHTTP` over the child, live and done, does not
panic).

(k8s 7f-4, Addendum T-k, producer (e)) Its causes: if `parent`'s causes are context errors or etcd's
no-leader error (`v3rpc.ctxCauseOk parent`), so are `ctx'`'s. The `*timerCtx` `c` (or the `*cancelCtx`
of the `WithCancel` case) is made by `WithDeadlineCause(parent, d, nil)`, so its own causes are its
errors (`cancel` stores `err` when the cause is nil): `Canceled` (the cancel function), `DeadlineExceeded`
(its timer, or `d` already passed); else `propagateCancel` stores `Cause(parent)` (`parent` already done)
or the found `*cancelCtx` `p`'s `cause` (`p`'s `cancel` passes it to its children, `:550-575`), each a
cause error by `ctxCauseOk parent`. `c.Value(&cancelCtxKey)` returns its embedded `cancelCtx` (i), and
`c.Err()` returns a non-nil error only once `c.Done()` is closed (an atomic load of `err`, then
`<-c.Done()`, go1.27.3 `:464-471`), which `cancel` does under `c.mu` after it assigned `cause`
(`:446-457, 550-575`), and `Cause` reads `cause` under `c.mu` after that `Err()` returned (ii). Go evidence: `TestCauseCancellable` (a `WithTimeout` child of the
wrapper and of a `WithValue` of it: `Cause` is `ErrGRPCNoLeader`, `Canceled` or `DeadlineExceeded`).

Not claimed: anything of `parent` beyond `srvCtxWeak`; the child's `Err` before `Done` is not
claimed nil (its timer or a cancel may have stored the error first). -/
axiom v3rpc.wp_WithTimeout_weak (parent : GoInterfaceOk) (pd : context.ContextDesc (IProp GF))
    (timeout : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ srvCtxWeak parent pd ∗
        levelTok v3rpc.ctxErrLvl ∗ v3rpc.ctxCauseOk parent }}
      (App (App (Val (@! _root_.Perennial.context.WithTimeout)) (Val #(interface.ok parent)))
        (Val #(timeout)))
    {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc) (d : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        levelTok v3rpc.ctxErrLvl ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        v3rpc.ctxChildErr ctx'
          { pd with Deadline := some d, PDone := iprop(True), Done_gn := γ' } ∗
        context.ctxValueFrom parent ctx' ∗ v3rpc.ctxCauseOk ctx' }}

end axiom_

end EtcdGrove
end Perennial
