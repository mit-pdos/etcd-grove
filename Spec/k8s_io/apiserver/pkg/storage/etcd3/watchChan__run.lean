/-
`(*watchChan).run(initialEventsEndBookmarkRequired, forceInitialEvents)`
(`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:269-292`), the watch's main goroutine (k8s 7f-5b,
`notes/k8s-7f5b-draft.md` §4): makes `watchClosedCh` (a broadcast of `kProdExited`), starts the producer
(`resultChanWG.Add(1); go { defer Done(); startWatching(...) }`) and the processing side
(`processEvents(&resultChanWG)`), waits until the producer has exited or `wc.ctx` is done, cancels
`wc.ctx` (`kCancelPD`: the producer exited, or the context is done), waits for the wait group (the
goroutines give back their fractions of `alive`) and closes `resultChan` (`kRes_close_au`). Its premises:
startWatching's (the caller's read laws, the store, the producer's ghost state and `initialRev`) and
the processing side's (`kWcCons`, `kProcSt` with the whole `alive`), with serialProcessEvents' read laws,
and a thread bound for its wait group (`rwg`, three top-level slots); its thread token comes back.
Lean-first (no Rocq counterpart).
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
abbrev watchChan.run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (r0 : w64),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
    kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  (m.bmReq = true → m.forceInit = true) →
  (c.pathPrefix ++ c.resourcePrefix).length ≤ opKeyMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ rangeStreamOff ∗
      isStore sp c ∗ kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r0 ∗
      kStartPre m Q r0 ∗ readAus c γk (Q 0) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) ∗
      kProdSt γ cd [] ∗ dghostVar γ.prodEx (DFrac.own 1) false ∗ kProcSt γ procd alive 1 ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ threadTok }}
    (App (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"run")) (Val #m.bmReq)) (Val #m.forceInit))
  {{ RET #(); threadTok }}

end spec

end k8s
end EtcdGrove
end Perennial
