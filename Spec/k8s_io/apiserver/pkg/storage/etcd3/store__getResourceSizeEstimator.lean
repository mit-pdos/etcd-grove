/-
`(*store).getResourceSizeEstimator()` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:279-283`):
under `collectorMux.RLock`, the estimator, `nil` (`isStore`'s reader pool guards
`resourceSizeEstimator ↦ nil`: nothing in the verified programs calls
`EnableResourceSizeEstimation`). The reader token is borrowed with the caller's thread token and
given back. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.5, a callee of `getList`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

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
abbrev store.getResourceSizeEstimator.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      threadTok }}
    (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
      go!"getResourceSizeEstimator")) (Val #()))
  {{ RET #(null : Loc); threadTok }}

end spec

end k8s
end EtcdGrove
end Perennial
