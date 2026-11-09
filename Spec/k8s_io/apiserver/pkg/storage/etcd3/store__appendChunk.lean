/-
`(*store).appendChunk(ctx, kvs, pred, newItemFunc, aggregator, v, paging)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:1055-1079`) of a chunk whose values all read as
objects (`kvWfHist`'s), with mod revisions that are non-negative, at most `2 ^ 41` of them: the
items grow by `growSlice`, then each key-value is evaluated (`processListItem`) until the limit is
reached (`chunkL`: 7e-3a's loop step, stopping at `more`), and freed (`kvs[i] = nil`: the slice is
owned). The post gives the count `n` of key-values evaluated, the last of their keys
(`lastKeyIs`), all of them unless the limit was reached, and, when the limit is reached or full,
that key is the loop's last match. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.4, with the
forms settled at Prove: the length and mod-revision premises, `n`). Lean-first (no Rocq
counterpart).
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
abbrev store.appendChunk.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ctx : GoInterface) (ksl : GoSlice) (ps : List Loc) (kvs : List EtcdKv)
    (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (nf : GoFunc) (ag : GoInterface) (v : _root_.Perennial.reflect.Value) (p : Loc)
    (paging : Bool) (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)),
  (∀ kv ∈ kvs, c.S.dec kv.value ≠ none) → (∀ kv ∈ kvs, 0 ≤ sint.Z kv.modRev) →
  kvs.length ≤ 2 ^ 41 → paging = decide (0 < sint.Z pred.Limit') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ newItemOk c.S nf ∗ ctxNeverDone ctx ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) p⌝ ∗ ksl ↦* ps ∗
      ([∗list] q;kv ∈ ps;kvs, txn.kvIs q kv) ∗
      (∃ s, p ↦ s ∗ L.itemsAt s (itemsOf c st)) ∗ ⌜st.more = false⌝ }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"appendChunk")) (Val #ctx)) (Val #ksl))
      (Val #pred)) (Val #nf)) (Val #ag)) (Val #v)) (Val #paging))
  {{ (lk : GoSlice) (evd : w64) (lr : Bool), RET (PairV (PairV (PairV #lk #evd) #lr) #GoInterface.nil);
      let st' := chunkL (fun x => sel x.1) (limN pred.Limit') st (decodedL c.S.dec kvs)
      iprop(⌜lr = st'.more⌝ ∗ (∃ ps' : List Loc, ksl ↦* ps') ∗ (∃ s, p ↦ s ∗ L.itemsAt s (itemsOf c st')) ∗
      ∃ n : Nat, ⌜n ≤ kvs.length ∧ evd = W64 (n : Int) ∧ (lr = false → n = kvs.length) ∧
        (0 < n → (lr = true ∨ 0 < limN pred.Limit' ∧ limN pred.Limit' ≤ st'.items.length) →
          ∃ kv, kvs[n - 1]? = some kv ∧ st'.last = some kv.key)⌝ ∗
        lastKeyIs lk kvs n) }}

end spec

end k8s
end EtcdGrove
end Perennial
