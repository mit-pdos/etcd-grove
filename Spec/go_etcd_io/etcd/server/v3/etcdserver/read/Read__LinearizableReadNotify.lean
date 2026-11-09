/-
## `(*Read).LinearizableReadNotify(ctx)`

**Users.** The server's linearizable reads: `EtcdServer.Range`, `RangeStream`, a read-only `Txn`
(`v3_server.go:139,175,346`), `Authenticate` (`v3_server.go:838`), `EtcdServer.
LinearizableReadNotify` (`interface.go:46`: the corruption checker's hasher, `corrupt.go:187`), the
lease HTTP handler (`server.go:688`), `server.go:924,1695` (the lease checkpoint and the
downgrade's reads). Concurrent callers, each with its own context (a gRPC request's, or
`context.Background()`-derived). Snippets: `examples/specreq/etcdserverreq/read.go`
(`ReqReadAfterWrite`, `ReqReadErrIndef`).

**Proof sketch.** `RLock` (the reader slot from the caller's `threadTok`), read `r.notifier` (the
current round `nc`), and, in the same atomic step as the read (the `RLock`'s invariant), deposit
`committedLb rγ l0` in the round's set of bounds (still open: the loop swaps a round only under
the write lock); `RUnlock`. A non-blocking send on `waitC` (either case: no resource). The `select`:
`nc.c` closed (the round's close: `nil` with the frozen set's guarantee, which contains `l0`; or the
loop's error, a `readErr`), `ctx.Done()` (`Context.doneRecv`: its `Err()` is `Canceled` or
`DeadlineExceeded`, `Context.ErrDone`), `r.server.Done()` (`readEnv`'s `Done`: `ErrStopped`). A
context with no `Done` channel (`Background`) is never chosen.

**Changes.** The old spec (`specs-ref`'s `Read__LinearizableReadNotify.lean`) took raft's names,
a saved predicate `g` of the caller's `Q`, the KV update's deposit `kvDep` and a reader slot, and
gave raft's witness `readServed` of the round's update at a read index at least `c`. Restated over
R1's vocabulary only: the caller's lower bound in, a committed log covering it (in operations) and
the member's applied index at it out. What the caller does with it (the server: its read
registry, `EtcdServer.srvRead`) is the caller's.

**Margin.** The index is at least the bound in raft terms too (raft's read index is the leader's
commit index once it committed in its term); stated in operations only, which is what R1's
`readState_fire` gives and what a state machine over `opsOf` needs.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

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

/-- **A linearizable read's wait**: `nil` once the member has applied a committed log whose
operations extend the caller's lower bound `l0` (known committed before the call); else one of the
read path's errors (indefinite). -/
def Read.LinearizableReadNotify.spec : Prop :=
  ∀ (r : Loc) (rγ : Raft.Cluster) (A : Nat → IProp GF) (ctx : GoInterface)
    (l0 : List Raft.LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗ readAt r rγ A ∗
      Context.ctxOk ctx ∗ Raft.committedLb rγ l0 ∗ threadTok }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
      go!"LinearizableReadNotify")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ l : List Raft.LogEntry, Raft.committedLb rγ l ∗ A l.length ∗
          ⌜Raft.opsOf l0 <+: Raft.opsOf l⌝) ∨
       readErr err) }}

end spec
end Read
end EtcdGrove
end Perennial
