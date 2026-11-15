/-
`(*watchChan).queueEvent(e)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:827-834`): sends `e` on
`incomingEventChan`, or gives up once `wc.ctx` is done; then records the wait in the incoming-event
block logger. Stated over the channel and an abstract send commit for `e` (as in `sendEvent`'s spec: the
producer builds the element's resource at the commit, so that a dropped event leaves no ghost trace),
offered as an Iris conjunction with the resources `S` it captures, and any context descriptor `cdw` of
`wc.ctx`: `Q` (sent), or `S` back and the context done (`□ cdw.PDone`). The producer (`startWatching`, step 5) takes `cdw := { cd with PDone := cd.PDone ∨
kCancelPD γ cd }` (the premise of 7f-5a-P's steps 4-5, `notes/k8s-7f5a-draft.md` §10) and turns a drop
into `kCancelled γ cd ∨ kProcExited γ`. Proved (k8s 7f-5a-P step 4; restated in the commit form at step 5:
with the element's resource taken before the send, a dropped event's raw-event index would already be
in `γ.raws`). Lean-first (no Rocq counterpart).
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
abbrev watchChan.queueEvent.spec : Prop :=
  ∀ (wc ch lg : Loc) (ctx : GoInterfaceOk) (cdw : context.ContextDesc (IProp GF)) (γch : ChanNames)
    (e : Loc) (S Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventChan" wc ↦□ ch ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ GoInterface.ok ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventLogger" wc ↦□ lg ∗
      blockLoggerOk lg ∗ context.isContext ctx cdw ∗ isChan ch γch Loc ∗
      (S ∧ (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Q -∗ Φ) -∗ sendAu γch e Φ)) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"queueEvent")) (Val #e))
  {{ RET #(); Q ∨ (□ cdw.PDone ∗ S) }}

end spec

end k8s
end EtcdGrove
end Perennial
