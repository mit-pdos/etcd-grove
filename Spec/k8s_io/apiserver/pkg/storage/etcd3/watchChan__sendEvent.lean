/-
`(*watchChan).sendEvent(event)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:813-825`): sends
`*event` on `resultChan`, or gives up once `wc.ctx` is done (returning `false`); then records the wait
in the result block logger. Stated over the channel and an abstract send commit (`Hsend`: the caller's
linearization of the send, three later credits and the continuation `Q`; `resultChan` has two producers,
so the commit is the caller's invariant's, `kResInv`, not the SPSC producer token) and any context
descriptor `cdw` of `wc.ctx`: `true` and `Q`, or `false`, `□ cdw.PDone` and the commit unused. Proved
(k8s 7f-5a-P step 4). Lean-first (no Rocq counterpart).
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
abbrev watchChan.sendEvent.spec : Prop :=
  ∀ (wc ch lg ev : Loc) (ctx : GoInterfaceOk) (cdw : context.ContextDesc (IProp GF)) (γch : ChanNames)
    (v : k8s_io.apimachinery.pkg.watch.Event) (dq : DFrac) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultChan" wc ↦□ ch ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ GoInterface.ok ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultLogger" wc ↦□ lg ∗
      blockLoggerOk lg ∗ context.isContext ctx cdw ∗
      isChan ch γch k8s_io.apimachinery.pkg.watch.Event ∗ ev ↦{dq} v ∗
      (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Q -∗ Φ) -∗ sendAu γch v Φ) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"sendEvent")) (Val #ev))
  {{ (b : Bool), RET #b; ev ↦{dq} v ∗
      ((⌜b = true⌝ ∗ Q) ∨
       (⌜b = false⌝ ∗ □ cdw.PDone ∗
         (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Q -∗ Φ) -∗ sendAu γch v Φ))) }}

end spec

end k8s
end EtcdGrove
end Perennial
