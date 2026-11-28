/-
`(*concurrentOrderedEventProcessing).scheduleEventProcessing(ctx, wg)`
(`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:611-635`), the concurrent branch's scheduler (k8s 7f-5b,
`notes/k8s-7f5b-draft.md` §3-§4): takes each raw event from `incomingEventChan` (`kInElem`), queues a new
response channel for it on `processingQueue` (`kQElem`, at the same index: the received and queued counts
are equal), and starts a goroutine that `transform`s it (no error: its values decode, `kRaw_transformOk`)
and sends the result on the response channel; each such goroutine is a member of `run`'s wait group,
added by the scheduler's top-level slot (`rwgDone`) with its level-`1` thread token (`rwg.wp_Add_member`),
which it gets back at the `go` statement (`rwg.wp_fork_member`). Returns when `ctx` (`wc.ctx`) is done.
Premises: the struct's `wc` and `processingQueue`, the watch channel's fields (`kWcCons`), the incoming
channel's consumer half and the queue's producer half (nothing received or queued yet), the read laws.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchConc

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
abbrev concurrentOrderedEventProcessing.scheduleEventProcessing.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (pp chQ : Loc) (γq : SpscNames) (wc sp : Loc)
    (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk)
    (kp : GoString) (recur : Bool) (wg : Loc) (P : IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜kvWfHist c σ ∧ kvWritesDec c σ ∧ kvRevFits σ.rev⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing go!"wc" pp ↦□
        wc ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing
        go!"processingQueue" pp ↦□ chQ ∗
      kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur ∗
      spscConsumer γ.inc ([] : List Loc) ∗
      isSpsc γq chQ (kQElem c W γ cd sel emp inS m Q) (fun _ => iprop(False)) ∗
      spscProducer γq ([] : List Loc) ∗ rwg.rwgDone rwgN 3 wg P ∗ levelTok 1 }}
    (App (App (Val (pp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing.ty @!!
      go!"scheduleEventProcessing")) (Val #(GoInterface.ok ctx))) (Val #wg))
  {{ RET #(); rwg.rwgDone rwgN 3 wg P ∗ levelTok 1 }}

end spec

end k8s
end EtcdGrove
end Perennial
