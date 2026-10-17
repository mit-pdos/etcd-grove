/-
`concurrency.waitDelete(ctx, client, key, rev)` (`client/v3/concurrency/key.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`waitDelete(ctx, client, key, rev, waitCh)`** (etcd#22387: it also receives from `waitCh`,
`waitDeletes`' watch of the waiter's own key `waitKey` from `wrev`, whose consumer it is given, and
gives back on `nil`: on an error `waitDeletes` returns, and a closed channel's consumer is gone), for a key under the client's prefix and a cancelable context (`WithCancel`):
* `nil` only after a delete event of `key` at a revision `r ≥ rev`, so `key` is absent from etcd's
  state at `r` (`isEtcdRangeWatcher`);
* `errWaitKeyDeleted` only after a delete event of `waitKey` on `waitCh`, at a revision `r ≥ wrev`,
  so `waitKey` is absent at `r`;
* otherwise an error (a watch's, the context's, or `errLostWatcher` when a channel closes). -/
abbrev waitDelete.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (client : Loc) (pfx key : GoString)
    (rev : w64) (waitCh : Loc) (γw : EtcdWatchNames) (waitKey : GoString) (wrev : w64)
    (rcv : List go_etcd_io.etcd.client.v3.WatchResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdMutexClient client pfx ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ waitKeyWatch γw waitCh pfx waitKey wrev ∗
      spscConsumer γw.spsc rcv ∗ ⌜pfx <+: key ∧ 0 ≤ sint.Z rev⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDelete))
      (Val #(GoInterface.ok ctx))) (Val #client)) (Val #key)) (Val #rev)) (Val #waitCh))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗
        (∃ rcv' : List go_etcd_io.etcd.client.v3.WatchResponse, spscConsumer γw.spsc rcv') ∗
        ∃ r : w64, etcdReached r ∗ etcdAbsent pfx key r ∗ ⌜sint.Z rev ≤ sint.Z r⌝) ∨
      (isPkgErr errWaitKeyDeleted err ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent pfx waitKey r ∗
        ⌜sint.Z wrev ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
