/-
`(*watchChan).queueEvent(e)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:827-834`): sends `e` on
`incomingEventChan`, or gives up once `wc.ctx` is done; then records the wait in the incoming-event
block logger. Stated over any SPSC protocol on the channel (`isSpsc`, the producer's half, the element's
resource `P` at its index) and any context descriptor `cdw` of `wc.ctx`: the event is sent (the
producer's history grows by `e`), or it is dropped, the element's resource is given back and the
context is done (`□ cdw.PDone`). The producer (`startWatching`, step 5) takes `cdw := { cd with PDone :=
cd.PDone ∨ kCancelPD γ cd }` (the premise of 7f-5a-P's steps 4-5, `notes/k8s-7f5a-draft.md` §10) and turns
a drop into `kCancelled γ cd ∨ kProcExited γ`. Proved (k8s 7f-5a-P step 4). Lean-first (no Rocq
counterpart).
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
  ∀ (wc ch lg : Loc) (ctx : GoInterfaceOk) (cdw : context.ContextDesc (IProp GF)) (γc : SpscNames)
    (P : Int → Loc → IProp GF) (R : List Loc → IProp GF) (sent : List Loc) (e : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventChan" wc ↦□ ch ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ GoInterface.ok ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventLogger" wc ↦□ lg ∗
      blockLoggerOk lg ∗ context.isContext ctx cdw ∗
      isSpsc γc ch P R ∗ spscProducer γc sent ∗ P sent.length e }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"queueEvent")) (Val #e))
  {{ RET #(); spscProducer γc (sent ++ [e]) ∨
      (spscProducer γc sent ∗ P sent.length e ∗ □ cdw.PDone) }}

end spec

end k8s
end EtcdGrove
end Perennial
