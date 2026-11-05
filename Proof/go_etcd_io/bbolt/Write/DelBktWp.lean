/-
U7m (`notes/bbolt-proof-plan.md`): **the root bucket's `DeleteBucket`** over the writer's records
in mode `false` (`wtxW`, the exclusive part taken out: `Write/DelBktXcl`) and its database side
(`wdbW`, for `child.free()`), for `Tx.DeleteBucket`.

The not-found post has a second case: for the empty name in an empty root bucket, `c.seek` returns
no key (`nil`), `bytes.Equal(newKey, nil)` holds for the empty `newKey`, and the zero flags give
`ErrIncompatibleValue`, not `ErrBucketNotFound` (U7m's finding; `Tx.DeleteBucket.spec` states
`ErrBucketNotFound` for every absent name).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktXcl
public import Proof.go_etcd_io.bbolt.Write.CreateBktWp
public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_w
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.Bucket__free
public import Proof.go_etcd_io.bbolt.Read.PubWCur

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What a successful `DeleteBucket` of the present `n` gives of the new records `X'` and database
side `w'`, from `X` and `w`: the facts `boltTxDef` closes with at `T.dropBkt n`, the view and meta
copy kept, the committed state kept, the freelist's agreement and the page tokens; and the cursor's
writer facts (`wrCurFacts`, maintainer 16's addition to `boltTx`'s writer facts: the deleted bucket
out of `liveB` and the root's `bm`, `n`'s generation bumped so `wRoot n = 0`, the other buckets'
`nm`, `nloc` and `ib.root'` unchanged). -/
def deleteOK (T : TxView) (r : TxReg) (n : GoString) (X X' : WX) (w w' : WDb) : Prop :=
  wOK X' ∧ wtxData X' = T.cur.delete n ∧ gensOK (T.dropBkt n) X' ∧ wrFacts X' ∧
    X'.v = X.v ∧ X'.t.mv = X.t.mv ∧ w'.C = w.C ∧ flViewU X' w'.fl ∧
    (∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) ∧
    wrCurFacts (T.dropBkt n) X'

omit package_sem in
/-- **The root bucket's `DeleteBucket`.** -/
theorem Bucket.DeleteBucket.wp_root
    (hBw : Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hFeb : Bucket.ForEachBucket_w.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hFree : Bucket.free.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb) (T : TxView) (name : GoSlice)
    (n : GoString) (dq : DFrac) (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X)
    (hwr : wrFacts X) (hwc : wrCurFacts T X) (hfl : flViewU X w.fl) :
  {{ wtxW (GF := GF) K tx r false X ∗ wdbW K tx X.v w ∗ name ↦*{dq} n }}
    (App (Val (X.rl @!! go.GoType.PointerType Bucket.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      (if T.cur.lookup n = none then
         iprop(wtxW K tx r false X ∗ wdbW K tx X.v w ∗
           (globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err ∨
            ⌜n = []⌝ ∗ globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue ↦□ err))
       else iprop(⌜err = GoInterface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb), wtxW K tx r false X' ∗
         wdbW K tx X.v w' ∗ ⌜deleteOK (GF := GF) T r n X X' w w'⌝)) }} := by
  sorry

end proof

end Write

end bbolt
end EtcdGrove
end Perennial
