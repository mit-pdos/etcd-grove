/-
`(*watchChan).Stop()` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:294-296`): `wc.cancel()`, whose
`Done` proposition (`kCancelPD`) the consumer's stop gives (`kStopped`; k8s 7f-5b, `notes/k8s-7f5b-draft.md`
§4): the first call takes `kLive`, a later one `kStopped`. Lean-first (no Rocq counterpart).
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
abbrev watchChan.Stop.spec : Prop :=
  ∀ (wc : Loc) (cf : GoFunc) (γc : context.ContextNames) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)),
  {{ structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"cancel" wc ↦□ cf ∗
      context.cancelSpec cf γc (kCancelPD γ cd) ∗ (kLive γ ∨ kStopped γ) }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"Stop")) (Val #()))
  {{ RET #(); kStopped γ }}

end spec

end k8s
end EtcdGrove
end Perennial
