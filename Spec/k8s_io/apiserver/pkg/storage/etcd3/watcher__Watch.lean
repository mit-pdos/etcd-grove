/-
`(*watcher).Watch(ctx, key, rev, opts)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:142-163`; k8s 7f-5b,
`notes/k8s-7f5b-draft.md` §4): with the prepared key `kp` (a recursive one ends with `/`) and
`ProgressNotify` off, the start revision (`getStartWatchResourceVersion`: the requested one, or with
`SendInitialEvents = false` at revision 0 the current one, `GetCurrentResourceVersion`, whose error is
returned), the watch channel (`createWatchChan`), its main goroutine (`go wc.run(...)`, at the mode
`kModeOf`), APF's initialization signal (`WatchInitialized`, which calls nothing at this context); returns
the error, or `nil` and the consumer's view (`k8sWatch`). Its premises: store.Watch's, at the
require-leader context (`isContext`, grpc's outgoing metadata, client errors, the initialization
signal's value) and the prepared key. Not the client's `watcher.Watch` (`EtcdGrove.watcher.Watch.spec`,
`Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean`): inside `namespace k8s` this name shadows it.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchCons
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

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
abbrev watcher.Watch.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wp sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (kp : GoString) (n : w64) (opts : k8s_io.apiserver.pkg.storage.ListOptions) (sie : Option Bool)
    (sel : Obj → Bool) (emp : Bool) (Q : Nat → KVState → IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
    kvRevFits σ.rev⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  c.pfx <+: kp → kp ≠ [] → kp.length ≤ opKeyMax → (opts.Recursive' = true → go!"/" <:+ kp) →
  uint.Z n < 2 ^ 63 - 1 → opts.ProgressNotify' = false → opts.RecordTimestamps' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (isStore sp c ∗
      storeWatchOk sp c W γk ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"watcher" sp ↦□ wp ∗
      sendInitIs opts.SendInitialEvents' sie ∗ selPredOk c.S opts.Predicate' sel emp ∗
      watchListOn ∗ rangeStreamOff ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
      context.valueAt ci flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (sem := sem)) ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ readAus c γk (Q 0) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev))) }}
    (App (App (App (App (Val (wp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.watcher.ty @!! go!"Watch")) (Val #(GoInterface.ok ci)))
      (Val #kp)) (Val #n)) (Val #opts))
  {{ (wi err : GoInterface), RET (PairV #wi #err); levelTok 0 ∗ (⌜err ≠ GoInterface.nil ∧ sie = some false ∧ uint.nat n = 0⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γ : KWatchNames,
        k8sWatch c W wi γ cd sel emp (kInScope kp opts.Recursive')
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q)) }}

end spec

end k8s
end EtcdGrove
end Perennial
