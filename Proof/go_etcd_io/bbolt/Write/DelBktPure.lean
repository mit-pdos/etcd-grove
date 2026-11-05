/-
U7o (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s records, pure** (the root bucket's
`DeleteBucket` of a present name `n`, `Write/DelBktWp`). The ghost steps, in the code's order:
1. `child := b.Bucket(newKey)`: `X1`, the child `c` (record `C`) opened in the root's cache `R1`
   (`dbk_opened`);
2. `delete(b.buckets, key)`, the child made dead (`killBkt`) and its caches nil: `delMid X1 c C R1 n D`
   (`D` the dead record: `deadRec`, then after `child.free()` its root `0`); well-formed
   (`wOK_delMid`): the root's entry `n` is no longer opened, its tree's keys from `bktNested`;
3. `child.free()`'s premises (`dbk_freePre`): the child's page tree in the view, its extents
   freeable;
4. `c.node().del(newKey)` after `Cursor.node`'s materializations `matGrow X5 X6 X.rl`: the key is
   in the leaf (`dbk_found`), and the records `X7` close `deleteOK0` (`dbk_post`: the records'
   facts by `Write/DelBktPost2.dbk_core`, the freelist's agreement by `Write/DelBktFlv.dbk_flView`,
   the page tokens by `Write/DelBktShape.dbk_shape`; the cursor's writer facts, `wrCurFacts`, are
   `DelBktWp`'s).
The proofs are in `Write/DelBktPlain`, `DelBktOpen`, `DelBktFound`, `DelBktFree`, `DelBktWOk`,
`DelBktPost`, `DelBktPost2` (U7p), `DelBktFlv`, `DelBktShape` (U7q).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktHeap
public import Proof.go_etcd_io.bbolt.Write.DelBktPlain
public import Proof.go_etcd_io.bbolt.Write.DelBktOpen
public import Proof.go_etcd_io.bbolt.Write.DelBktFound
public import Proof.go_etcd_io.bbolt.Write.DelBktFree
public import Proof.go_etcd_io.bbolt.Write.DelBktWOk
public import Proof.go_etcd_io.bbolt.Write.DelBktPost2
public import Proof.go_etcd_io.bbolt.Write.DelBktFlv
public import Proof.go_etcd_io.bbolt.Write.DelBktShape
public import Proof.go_etcd_io.bbolt.Write.DelBktPath
public import Proof.go_etcd_io.bbolt.Write.DelBkt
public import Proof.go_etcd_io.bbolt.Write.WOkLeafPut
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt
public import Proof.go_etcd_io.bbolt.Model.RTree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common


section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What a successful `DeleteBucket` of the present `n` gives of the new records `X'` and database
side `w'`, from `X` and `w`, but the cursor's writer facts (`DelBktWp.deleteOK`): the facts
`boltTxDef` closes with at `T.dropBkt n`, the view and meta copy kept, the committed state kept,
the freelist's agreement and the page tokens. -/
def deleteOK0 (T : TxView) (r : TxReg) (n : GoString) (X X' : WX) (w w' : WDb) : Prop :=
  wOK X' ∧ wtxData X' = T.cur.delete n ∧ gensOK (T.dropBkt n) X' ∧ wrFacts X' ∧
    X'.v = X.v ∧ X'.t.mv = X.t.mv ∧ w'.C = w.C ∧ flViewU X' w'.fl ∧
    (∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra)

/-- **`DeleteBucket`'s post** (see the module doc). -/
theorem dbk_post (T : TxView) (r : TxReg) (X X1 X6 : WX) (c : Loc) (C R1 : BRec) (n : GoString)
    (D : BRec) (w w' : WDb) (l : Loc) (B6 : BRec) (rl : NRec) (s : GoSlice) (ins : List Inode)
    (t : RTree)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hfl : flViewU X w.fl) (hsome : T.cur.lookup n ≠ none)
    (hok1 : wOK X1) (hd1 : wtxData X1 = wtxData X) (hR1 : X1.t.bs !! X.rl = some R1)
    (hn : R1.bm !! n = some c) (hC : X1.t.bs !! c = some C) (hcr : c ≠ X.rl) (hrl1 : X1.rl = X.rl)
    (hv1 : X1.v = X.v) (hmv1 : X1.t.mv = X.t.mv) (hgens1 : gensOK T X1) (hwr1 : wrFacts X1)
    (hfl1 : flViewU X1 w.fl) (hdo1 : objsDisj X1.t) (htx : X1.t.mv.txid' = w.wtxid)
    (hsh1 : ∀ γ extra, txShape (GF := GF) γ X extra ⊢ txShape γ X1 extra)
    (hD : (C.ib.root' = W64 0 ∧ D = deadRec { C with ns := ∅ } ∧ w' = w) ∨
      (C.ib.root' ≠ W64 0 ∧ ltIs (pltree X1.v) c t ∧ t.pid = C.ib.root' ∧
        D = { deadRec { C with ns := ∅ } with ib := { C.ib with root' := W64 0 } } ∧
        w' = w.withFl (w.fl.freeAll w.wtxid (t.pos.filterMap (pExt X1.v)))))
    (hmg : matGrow (delMid X1 c C R1 n D) X6 X.rl) (hok6 : wOK X6) (hd6 : objsDisj X6.t)
    (hB6 : X6.t.bs !! X.rl = some B6) (hrl : B6.ns !! l = some rl) (hlf : leafFor X6 X.rl n l)
    (hfd : wsFound rl.ws n) (hins : ins.length = (wsDelAt rl.ws n).length) :
    deleteOK0 (GF := GF) T r n X (X6.setNode X.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true))
      w w' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := dbk_core T X X1 X6 c C R1 n D l B6 rl s ins hcur hok1 hd1 hR1
    hn hC hrl1 hv1 hmv1 hgens1 hwr1 hdo1 hfl1.2.2.1 hmg hok6 hd6 hB6 hrl hlf hins
  have hC' : w'.C = w.C := by
    rcases hD with ⟨-, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> rfl
  refine ⟨c1, c2, c3, c4, c5, c6, hC', ?_, fun extra => (hsh1 _ extra).trans ?_⟩
  · rw [← hrl1] at hR1 hmg hB6 hlf ⊢
    exact dbk_flView X1 X6 c C R1 n D w w' l B6 rl s ins t hok1 hR1 hn hC hwr1 hfl1 htx
      (wOK_delMid T X1 c C R1 n D hok1 hwr1 hgens1 hR1 hn hC hdo1 hfl1.2.2.1) hD hmg hok6 hB6 hrl hlf
  · rw [← hrl1] at hR1 hmg hB6 hlf ⊢
    rw [← hrl1] at c1 c4
    exact dbk_shape (GF := GF) _ X1 X6 c C R1 n D l B6 rl s ins hok1 hR1 hn hC hwr1 hdo1 hfl1.2.2.1
      hmg hok6 hB6 hrl hlf c1 c4 extra

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
