/-
`(*watchChan).prepareObjs(e)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:836-873`) of a queued
`*event` holding the raw event `r` at the state `σ` (`kEvIs`, read-only), whose values decode
(`kRawDecOk`, from `kvWfHist`): the current and old objects (`kCurObj`, `kOldObj`: decoded by
`TransformFromStorage` then `decodeObj`, at the event's revision; `nil` where Go leaves them), no
error (the error paths, and `transformIfCorruptObjectError`, need a value that does not read or
decode). The watch's fields read are read-only once made (`watcher`, `ctx`, `internalPred`, and the
watcher's `codec`, `versioner`, `transformer`). Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq
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
abbrev watchChan.prepareObjs.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (W : WatchSpec Obj) (codec : GoInterface)
    (vi ti : GoInterfaceOk) (wc wp : Loc) (ctx : GoInterface)
    (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (ep : Loc) (x : k8s_io.apiserver.pkg.storage.etcd3.event) (σ : KVState) (r : KRaw),
  kRawDecOk S.dec σ r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"watcher" wc ↦□ wp ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ ctx ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"internalPred" wc ↦□ p ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"codec" wp ↦□ codec ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"versioner" wp ↦□
        GoInterface.ok vi ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"transformer" wp ↦□
        GoInterface.ok ti ∗
      selPredOkW S p sel emp ∗ transformerOk S ti ∗ versionerOk S vi ∗ watchContractOk S W codec ∗
      ep ↦□ x ∗ kEvIs σ x r }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"prepareObjs")) (Val #ep))
  {{ (cur old err : GoInterface), RET (PairV (PairV #cur #old) #err);
      ⌜err = GoInterface.nil⌝ ∗ kObjOpt S cur (kCurObj S.dec r) (kRawRev r) ∗
      kObjOpt S old (kOldObj S.dec emp σ r) (kRawRev r) }}

end spec

end k8s
end EtcdGrove
end Perennial
