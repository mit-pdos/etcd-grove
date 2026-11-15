/-
`(*store).finalizeList(listObj, pred, rev, continueValue, remainingItemCount, aggregator, v)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:1005-1018`): a fresh aggregator's `Aggregate()` is
`nil`; a `nil` items slice (`IsNil`, empty by its post) becomes an empty one (`MakeSlice`, `Set`);
the versioner's `UpdateList` writes the list's metadata (`listContractOk`); `SetShardInfoOnList` is
a no-op (no shard selector, `selPredOk`). The list then holds the items with the metadata given.
Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.6). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs

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
abbrev store.finalizeList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc)
    (c : StoreCfg GF Obj) (L : ListSpec GF Obj) (lx : GoInterface) (pl : Loc)
    (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (rev : w64) (cont : GoString) (rem : Loc) (remV : Option w64) (ag : GoInterface)
    (v : _root_.Perennial.reflect.Value) (os : List (Obj × GoString)) (rv0 : w64)
    (cont0 : GoString) (rem0 : Option w64),
  lx = interface.mkOk (go.GoType.PointerType L.listTy) #pl →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ freshAggr ag ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) (L.itemsRef pl)⌝ ∗
      L.listAtItems pl os rv0 cont0 rem0 ∗ remIs rem remV }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"finalizeList")) (Val #lx)) (Val #pred))
      (Val #rev)) (Val #cont)) (Val #rem)) (Val #ag)) (Val #v))
  {{ RET #GoInterface.nil; L.listAt lx os rev cont remV }}

end spec

end k8s
end EtcdGrove
end Perennial
