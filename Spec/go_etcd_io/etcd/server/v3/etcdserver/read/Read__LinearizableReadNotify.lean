/-
`read.Read.LinearizableReadNotify(ctx)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `r.LinearizableReadNotify(ctx)` with a lower bound `c` of the committed index the caller knew of
and a reader slot of `r.mux` (given back): `nil` only once the applied index has reached an index
at least `c` (`readIndexOk`): the notifier the caller waited on was swapped out after it deposited
`c` in its need, and the loop closed it with `nil` only after the applied index passed a read
index issued after the swap; else an error the gRPC layer can take: the notifier's (the loop's
`requestCurrentIndex` error), the context's (`Canceled`, `DeadlineExceeded`), or the server's
`ErrStopped`. A context with a `nil` `Done()` (`mvcc.txnCtx`'s other case) is never done.
(2026-10-14, unit T1) The caller registers its result predicate `Q` (a saved predicate at `g`)
with its `Get` update (`kvDep`) in the notifier's clients' list, and on `nil` learns its read
served (`readServed`: raft's witness of the round's update at a read index at least `c`). -/
abbrev read.Read.LinearizableReadNotify.spec : Prop :=
  ∀ (r : Loc) (γr : ReadNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (c : w64) (g : GName) (Q : List EntryModel → IProp GF) (F : List EntryModel → KVState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      isReadPre r γr F ∗ mvcc.txnCtx ctx cd ∗ committedAtLeast γr c ∗ readReader r γr ∗
      savedPredOwn g DFrac.discard Q ∗ kvDep γr.kv Q F }}
    (App (Val (r @!! go.GoType.PointerType Read.ty @!! go!"LinearizableReadNotify"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; readReader r γr ∗ applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ readIndexOk γr c ∗ readServed γr c g) }}

end spec

end EtcdGrove
end Perennial
