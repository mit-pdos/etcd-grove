/-
`(*watchChan).serialProcessEvents(wg)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:554-576`), the
watch's processing goroutine when `ConcurrentWatchObjectDecode` is off (k8s 7f-5b, `notes/k8s-7f5b-draft.md`
§4): receives each raw event from `incomingEventChan` (`kInElem`), `transform`s it (no error: its values
decode, `kRaw_transformOk`) and sends the result on `resultChan` (`sendEvent`; a filtered one is skipped),
recording each step in `kResInv` (`kRes_evCommit`, `kRes_filterStep`); returns when `wc.ctx` is done or a
send gives up, its deferred `wg.Done()` passing the alive fraction to `run`'s `Wait` (a top-level slot of
`run`'s wait group, `rwgDone`). Its premises: the watch channel's fields (`kWcCons`), the processing
side's resources (`kProcSt`), the caller's read laws (the read states' values decode and their revision
fits; one history), the goroutine's thread token. Lean-first (no Rocq counterpart).
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
abbrev watchChan.serialProcessEvents.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (q : Qp) (wg : Loc),
  (∀ lb σ, Q lb σ ⊢ ⌜kvWfHist c σ ∧ kvWritesDec c σ ∧ kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      kWcCons wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur ∗
      kProcSt γ procd alive q ∗ rwg.rwgDone rwgN 3 wg (kResAlive alive q) ∗ threadTok }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"serialProcessEvents")) (Val #wg))
  {{ RET #(); threadTok }}

end spec

end k8s
end EtcdGrove
end Perennial
