/-
`(*store).processListItem(ctx, kv, pred, newItemFunc, aggregator, v)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:1020-1053`) of a key-value whose value reads as the
object `o` (`kvWfHist`'s): the transformer's data (`transformerOk`), the `ctx.Done()` select's
default (`ctxNeverDone`), the decoder's `DecodeListItem` (`listContractOk`), `pred.Matches`
(`selPredOk`), and, if it matches, `reflect.Append` of the object (`listContractOk'`) set into the
items (`Value.Set`). The aggregator is not reached. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md`
§3.4). Lean-first (no Rocq counterpart).
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
abbrev store.processListItem.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ctx : GoInterface) (kvp : Loc) (kv : EtcdKv)
    (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) (nf : GoFunc) (ag : GoInterface)
    (v : _root_.Perennial.reflect.Value) (p : Loc)
    (s : GoSlice) (os : List (Obj × GoString)) (o : Obj),
  (∃ b, c.S.dec kv.value = some (o, b)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ newItemOk c.S nf ∗ ctxNeverDone ctx ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) p⌝ ∗ txn.kvIs kvp kv ∗ p ↦ s ∗ L.itemsAt s os }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"processListItem")) (Val #ctx))
      (Val #kvp)) (Val #pred)) (Val #nf)) (Val #ag)) (Val #v))
  {{ RET (PairV #true #GoInterface.nil); ∃ s', p ↦ s' ∗
      L.itemsAt s' (if sel o then os ++ [(o, c.S.fmtRV kv.modRev)] else os) }}

end spec

end k8s
end EtcdGrove
end Perennial
