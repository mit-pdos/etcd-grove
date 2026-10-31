/-
`store.compactBarrier` (`kvstore.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compactBarrier(ctx, ch)` with the close right on `ch` (closed with `Q`, which holds) and a
share of the store's fields at the objects `o` (the running job's lease, `storeStopR_lease`; M2,
the storage side, item 17: until then the discarded `storeStop`), given back: if the context is
not cancelled, `ch` closed; if it is, the scheduler was stopped, whose payload is the stop channel
closed (`□ (cd.PDone -∗ schedPay γ.sch)`, the job contract's, `stopPayAt`), so the receive on
`s.stopc` is ready and the barrier returns: the re-scheduling branch (`s.mu`, `Schedule`) is dead
(`Restore` and `Close` close `stopc` before `Stop` cancels the context, etcd PR 11817's order). -/
abbrev mvcc.store.compactBarrier.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ch : GoChan) (Q : IProp GF) (q : Qp) (o : mvcc.StoreObjs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.fieldShareAt s γ q o ∗ mvcc.barrierCtx ctx cd ∗ □ (cd.PDone -∗ schedule.schedPay γ.sch) ∗
      mvcc.compactCloser ch Q ∗ □ Q }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactBarrier"))
      (Val #(GoInterface.ok ctx))) (Val #ch))
  {{ RET #(); mvcc.fieldShareAt s γ q o }}

end spec

end EtcdGrove
end Perennial
