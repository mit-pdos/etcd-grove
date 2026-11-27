/-
`(*watcher).createWatchChan(ctx, key, rev, recursive, progressNotify, recordTimestamps, pred)`
(`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:167-189`; k8s 7f-5b, `notes/k8s-7f5b-draft.md` §4): the
watch channel of the prepared key `kp` from `rev`, under `WithCancel(ctx)` (`wc.ctx`, whose Done
proposition adds `kCancelPD`), its predicate `pred`, or `storage.Everything` when `pred.Empty()`
(`selPredOkW`), its two channels and block loggers. Returns the fields the goroutines read (`kWcCons`),
`initialRev`, the producer's state (`kProdSt`, `prodEx`), the processing side's (`kProcSt`, the whole
`alive`), the consumer's half of `resultChan` and `kLive`, for any mode `m` and read updates `Q` (ghost
only). Its premises: the store and its watcher (`isStore`, `storeWatchOk`), the caller's context with
grpc's outgoing metadata, the predicate (`selPredOk`), the key under the store's prefix, not empty and
short. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchCons

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
abbrev watcher.createWatchChan.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wp sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (kp : GoString) (rev : w64) (recur : Bool) (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF),
  c.pfx <+: kp → kp ≠ [] → kp.length ≤ opKeyMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      storeWatchOk sp c W γk ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"watcher" sp ↦□ wp ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ selPredOk c.S pred sel emp }}
    (App (App (App (App (App (App (App (Val (wp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.watcher.ty @!! go!"createWatchChan"))
      (Val #(GoInterface.ok ci))) (Val #kp)) (Val #rev)) (Val #recur)) (Val #false)) (Val #false))
      (Val #pred))
  {{ (wc : Loc), RET #wc; ∃ (γ : KWatchNames) (procd alive : GName) (ctx : GoInterfaceOk),
      kWcCons wc sp c W γk γ cd sel emp (kInScope kp recur) m Q procd alive ctx kp recur ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ rev ∗
      kProdSt γ cd [] ∗ dghostVar γ.prodEx (DFrac.own 1) false ∗ kProcSt γ procd alive 1 ∗
      spscConsumer γ.res ([] : List k8s_io.apimachinery.pkg.watch.Event) ∗ kLive γ }}

end spec

end k8s
end EtcdGrove
end Perennial
