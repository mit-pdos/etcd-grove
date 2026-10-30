/-
`read.Read.LinearizableReadLoop()` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
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

/-- `r.LinearizableReadLoop()`, the read loop's goroutine, with the logger's resource `LR` and the
server's premise `□ |==> NR` (the id budget): it returns (the server stopping, or raft or the
server stopped), with nothing to give back. Its safety is the read invariant's (`readInv`):
a notifier is closed with `nil` only after its need was frozen and the applied index reached a
read index at least the frozen need. On `isStopped(err)` it returns without closing the pending
notifier: its waiters leave by their context or the server's `Done()` (Go's behavior). -/
abbrev read.Read.LinearizableReadLoop.spec : Prop :=
  ∀ (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → (List EntryModel → IProp GF) → IProp GF) (LR NR : IProp GF)
    (F : List EntryModel → KVState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      isReadLoopPre r γr RQ LR NR F ∗ LR ∗ □ (|==> NR) }}
    (App (Val (r @!! go.GoType.PointerType Read.ty @!! go!"LinearizableReadLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
