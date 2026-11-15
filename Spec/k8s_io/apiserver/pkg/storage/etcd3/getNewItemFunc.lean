/-
`getNewItemFunc(listObj, v)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:639-654`) of a list that
is not an `*unstructured.UnstructuredList`: a function making a fresh zero object (`newItemOk`):
`reflect.New` of the items' element type (`v.Type().Elem()`), its `Interface()`, asserted a
`runtime.Object` (`S.tyOk`). Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.2). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev getNewItemFunc.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (L : ListSpec GF Obj) (pl : Loc)
    (v : _root_.Perennial.reflect.Value),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      ⌜S.tyOk ∧ L.listTy ≠ k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty ∧
        reflElem v (go.GoType.SliceType S.objTy) (L.itemsRef pl)⌝ }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.getNewItemFunc))
      (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl : GoInterface))) (Val #v))
  {{ (f : GoFunc), RET #f; newItemOk S f }}

end spec

end k8s
end EtcdGrove
end Perennial
