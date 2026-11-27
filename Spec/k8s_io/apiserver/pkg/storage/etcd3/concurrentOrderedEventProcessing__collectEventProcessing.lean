/-
`(*concurrentOrderedEventProcessing).collectEventProcessing(ctx)`
(`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:637-660`), the concurrent branch's collector (k8s 7f-5b,
`notes/k8s-7f5b-draft.md` §3-§4): takes the response channels from `processingQueue` in order (`kQElem`:
the `i`-th one is for the `i`-th raw event of `incomingEventChan`), then each one's result, and sends it
on `resultChan` as `serialProcessEvents` does (`sendEvent`; a filtered one is skipped), recording each
step in `kResInv` (`kRes_evCommit`, `kRes_filterStep`). No result has an error (`kRcElem`), so the
`sendError` arm is dead. Returns when `ctx` (`wc.ctx`) is done or a send gives up, with the alive
fraction. Premises: the struct's `wc` and `processingQueue`, the watch channel's fields (`kWcCons`), the
queue's consumer half (nothing received yet), `procd`'s half at `0`, `procEx` at `false`, the alive
fraction, one history. Lean-first (no Rocq counterpart).
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
abbrev concurrentOrderedEventProcessing.collectEventProcessing.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (pp chQ : Loc) (γq : SpscNames) (wc sp : Loc)
    (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk)
    (kp : GoString) (recur : Bool) (q : Qp),
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing go!"wc" pp ↦□
        wc ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing
        go!"processingQueue" pp ↦□ chQ ∗
      kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur ∗
      isSpsc γq chQ (kQElem c W γ cd sel emp inS m Q) (fun _ => iprop(False)) ∗
      spscConsumer γq ([] : List Loc) ∗ dghostVar procd (DFrac.own (1 : Qp).half) 0 ∗
      dghostVar γ.procEx (DFrac.own 1) false ∗ kResAlive alive q }}
    (App (Val (pp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.concurrentOrderedEventProcessing.ty @!!
      go!"collectEventProcessing")) (Val #(GoInterface.ok ctx)))
  {{ RET #(); kResAlive alive q }}

end spec

end k8s
end EtcdGrove
end Perennial
