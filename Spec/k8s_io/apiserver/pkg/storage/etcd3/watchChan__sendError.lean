/-
`(*watchChan).sendError(err)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:793-811`): unless the
error is a cancellation, sends `transformErrorToEvent(err)` (an Error event whose object is a `Failure`
status, `statusFailureAt`) on `resultChan`, or gives up once `wc.ctx` is done; in every case calls
`wc.cancel()` (deferred). Stated over an error the watcher's error paths accept (`kErrOk`), the cancel
function's spec (`context.cancelSpec`, with its proposition `Pc` given: the caller has set its part of
`kCancelPD` first), the channel and an abstract send commit for any Error event (`Hsend`, as in
`sendEvent`'s spec), and any context descriptor `cdw` of `wc.ctx`: `Q` (sent), or the commit unused.
Proved (k8s 7f-5a-P step 4). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchChan.sendError.spec : Prop :=
  ∀ (wc ch : Loc) (ctx : GoInterfaceOk) (cdw : context.ContextDesc (IProp GF)) (γch : ChanNames)
    (cf : GoFunc) (γc : context.ContextNames) (Pc : IProp GF) (err : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultChan" wc ↦□ ch ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ GoInterface.ok ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"cancel" wc ↦□ cf ∗
      context.cancelSpec cf γc Pc ∗ □ Pc ∗ context.isContext ctx cdw ∗ kErrOk err ∗
      isChan ch γch k8s_io.apimachinery.pkg.watch.Event ∗
      (∀ v : k8s_io.apimachinery.pkg.watch.Event, ⌜v.Type' = go!"ERROR"⌝ -∗ statusFailureAt v.Object' -∗
        £ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Q -∗ Φ) -∗ sendAu γch v Φ) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"sendError")) (Val #err))
  {{ RET #(); Q ∨
      (∀ v : k8s_io.apimachinery.pkg.watch.Event, ⌜v.Type' = go!"ERROR"⌝ -∗ statusFailureAt v.Object' -∗
        £ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Q -∗ Φ) -∗ sendAu γch v Φ) }}

end spec

end k8s
end EtcdGrove
end Perennial
