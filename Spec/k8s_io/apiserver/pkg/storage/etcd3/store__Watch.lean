/-
`(*store).Watch(ctx, key, opts)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:1142-1152`; k8s 7f-5a,
`notes/k8s-7f5a-draft.md` §3, reviewed with the Draft; moved verbatim from the Draft file
`Draft7f5a.lean`, where it was `Draft.store.Watch.spec`, 2026-11-16, decided by etcd-grove-02). A
hypothesis of 7f-6 (branch `k8s-7f6`): any change goes through the ledger
(`notes/specs-only/ledger.md`). Not proved yet (7f-5a-P step 6). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Spec.k8s_io.klog.v2.Args

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

/-- **`(*store).Watch(ctx, key, opts)`** (`store.go:1142-1152`; see `notes/k8s-7f5a-draft.md` §3):
a watch of the prepared key's scope from the parsed resource version `n`, with `WatchList` on,
`EtcdRangeStream` off (either value of `ConcurrentWatchObjectDecode`), under the caller's
context (an `isContext` with grpc's outgoing metadata, client errors and the Kubernetes keys), with
the caller's read updates `Q lb` (`Q lb σ`: a state of one history at revision at least `lb`;
`Q σ.rev` handed out after a firing at `σ`; its states' revisions put only values that decode under
the store's prefix, `kvWritesDec`, and its revision fits an `int64`, `kvRevFits`: ledger, "store.Watch without `concurrentDecodeOff`"), returns an error (only `getCurrentStorageRV`'s, for RV 0 with `SendInitialEvents = false`), or `nil`
and the consumer's view
(`k8sWatch`, live while the caller has not stopped it and its context `cd` is not done). No thread
token: the watch's three goroutines get theirs at their `go` statements. -/
abbrev store.Watch.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (opts : k8s_io.apiserver.pkg.storage.ListOptions) (k : GoString) (n : w64)
    (sie : Option Bool) (sel : Obj → Bool) (emp : Bool) (Q : Nat → KVState → IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
    kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (isStore sp c ∗
      storeWatchOk sp c W γk ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        uint.Z n < 2 ^ 63 - 1 ∧ opts.ProgressNotify' = false ∧ opts.RecordTimestamps' = false⌝ ∗
      sendInitIs opts.SendInitialEvents' sie ∗ selPredOk c.S opts.Predicate' sel emp ∗
      watchListOn ∗ rangeStreamOff ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
      k8sctx.k8sCtxOk ci ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (|==> readAus c γk (Q 0)) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev))) }}
    (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Watch")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts))
  {{ (wi err : GoInterface), RET (PairV #wi #err); levelTok 0 ∗ (⌜err ≠ GoInterface.nil ∧ sie = some false ∧ uint.nat n = 0⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γ : KWatchNames,
        k8sWatch c W wi γ cd sel emp (kScopeOf c k opts.Recursive')
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q)) }}

end spec

end k8s
end EtcdGrove
end Perennial
