/-
`(*watchChan).acceptAll()` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:672-674`): whether the watch's predicate (`internalPred`, read-only once made, `selPredOk`) is empty. Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
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
abbrev watchChan.acceptAll.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (wc : Loc) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"internalPred" wc ↦□ p ∗
      selPredOk S p sel emp }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"acceptAll")) (Val #()))
  {{ RET #emp; True }}

end spec

end k8s
end EtcdGrove
end Perennial
