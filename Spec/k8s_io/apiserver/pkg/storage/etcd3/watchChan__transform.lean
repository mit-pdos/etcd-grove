/-
`(*watchChan).transform(e)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:677-760`) of a queued
`*event` holding the raw event `r` at the state `σ` (`kEvIs`, read-only) whose values decode
(`kRawDecOk`) and whose revision is not negative: `kRawToEv` of it, as a fresh `*watch.Event`
(`wevAt`), or `nil` when filtered out; no error. A bookmark's object is `newFunc()`'s zero object at
the bookmark's revision, annotated for the initial-events-end bookmark (`watchContractOk`); events are
not wrapped (`recordTimestamps` is false). The watch's fields read are read-only once made. Proved
(k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
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
abbrev watchChan.transform.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (W : WatchSpec Obj) (codec : GoInterface)
    (vi ti : GoInterfaceOk) (wc wp : Loc) (ctx : GoInterface) (nf : GoFunc)
    (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (ep : Loc) (x : k8s_io.apiserver.pkg.storage.etcd3.event) (σ : KVState) (r : KRaw),
  kRawDecOk S.dec σ r →
  (∀ v, r = .kv v → 0 ≤ sint.Z v.modRev) → (∀ e, r = .ev e → 0 ≤ sint.Z e.kv.modRev) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"watcher" wc ↦□ wp ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"internalPred" wc ↦□ p ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"recordTimestamps" wc ↦□ false ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"codec" wp ↦□ codec ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"newFunc" wp ↦□ nf ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"versioner" wp ↦□
        GoInterface.ok vi ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"transformer" wp ↦□
        GoInterface.ok ti ∗
      selPredOkW S p sel emp ∗ transformerOk S ti ∗ versionerOk S vi ∗ watchContractOk S W codec ∗
      newItemOk S nf ∗ ep ↦□ x ∗ kEvIs σ x r }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"transform")) (Val #ep))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err);
      ⌜err = GoInterface.nil⌝ ∗
      match kRawToEv S.dec sel emp S.zero σ r with
      | none => ⌜res = null⌝
      | some ev => ∃ v : k8s_io.apimachinery.pkg.watch.Event, res ↦ v ∗ wevAt S W v ev }}

end spec

end k8s
end EtcdGrove
end Perennial
