/-
`(*watchChan).filter(obj)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:664-670`) of an object `o`, the watch's predicate (`internalPred`, read-only once made) selecting by `sel` and empty iff `emp` (`selPredOkW`): `sel o` (an empty predicate selects everything), the object given back. Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
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
abbrev watchChan.filter.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (wc : Loc) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) (x : GoInterface) (o : Obj) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"internalPred" wc ↦□ p ∗
      selPredOkW S p sel emp ∗ S.objAt x o rv }}
    (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"filter")) (Val #x))
  {{ RET #(sel o); S.objAt x o rv }}

end spec

end k8s
end EtcdGrove
end Perennial
