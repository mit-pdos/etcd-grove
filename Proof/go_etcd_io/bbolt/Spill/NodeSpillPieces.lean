/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **`spillTail_wp`**,
the WP of `Spill/NodeSpillPiecesCode`'s `spillTail` (`n.children = nil`, the split, the pieces'
loop, the top case's recursion) from the state after the loop (`spEnd`) to `n`'s spill's post
(`spPost`), over Löb's hypothesis `spillIH` (the top case's `n.parent.spill()`).

How `node__spill` uses it: in the unspilled case, after the sort and the children's loop (whose
post gives `spEnd`), the goal is `WP (exceptionSeq (λ: <>, spillTail …) executeVal) {{ … }}`
inside `exceptionDo`; a pure step, `wp_bind (spillTail _ _ _)`, then `spillTail_wp`; its post's
`returnVal #()` finishes the `exceptionDo`, and the function returns the cell `resp`'s `err`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesCode
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesDefs
public import Proof.go_etcd_io.bbolt.Spill.Split
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.node__write
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.TxStats__IncSpill
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`node.spill` after its children's loop** (see the module doc). `np`, `txp`, `resp`: the
cells of `n`, `tx` (`n.bucket.tx`) and the result. -/
theorem spillTail_wp
    (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hSplit : node.split.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hKey : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase) (X' : WX) (w' : WDb) (r' : NRec) (st : List FLStep)
    (T : List Loc) (np txp resp : Loc) (e0 : GoInterface)
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    ⊢ □ ▷ spillIH (GF := GF) (hG := hG) -∗ wtxW K tx r m X' -∗ wdbW K tx X'.v w' -∗
      np ↦ n -∗ txp ↦ tx -∗ resp ↦ e0 -∗
      WP (spillTail np txp resp) {{ v, ⌜v = returnVal #()⌝ ∗ ∃ err : GoInterface,
        resp ↦ err ∗ np ↦ n ∗ txp ↦ tx ∗ spPost K tx r m X w bl n rn O lo hi h D N E cs err }} := by
  -- Not yet (U9l hand-off). The pieces done: `Spill/NodeSpillPiecesKill.wtxW_nilCh` (step 1,
  -- `n.children = nil`; pure: `spG`/`spFrame` of `WX.nilCh`, the kill framed by `spEnd`'s last
  -- clause and `spCtx`'s `rn.cs ⊆ N`); `Spill/NodeSpillPiecesOne.pieceOne_wp` (one piece's
  -- iteration, `pcStep`; its parent case still a `sorry`). Remaining:
  -- 2. `n.split(pageSize)` (`Spill/Split.node.split.spec`: `n`'s struct, inodes and capacity
  --    (`uNode`'s `capOwn`), the bucket's `FillPercent` (`node__rebalance`'s `Hfp` access) and
  --    `tx` field, `parentOwn` (the child case: `pl`'s object, `wtxHeap_setBkt_acc`)); the pieces
  --    back in the heap: `n`'s record and the parent's by `wtxHeap_reshape`, the fresh pieces
  --    (and the top case's new parent) by `wtxHeap_fresh` + `wtxHeap_node_insert`, their entries
  --    the `wOwn` list split as `(xs.map (·.2.2)).flatten = ins` (`capOwn := false`).
  -- 3. the pieces' loop: `slice.forRange` unfolds (`pure_wp_slice_for_range`) to `wp_for` over
  --    `i`; each iteration `pieceOne_wp` (its premises from the loop's invariant: the slots
  --    owned (`slotInv` of `O ++` the done pieces' `pcSlots` `++` the rest's), so the allocated
  --    id is no child's and below the mark (`hid`); `spG` after the free (`hG`)); the invariant
  --    (pure, to write) tracks the done pieces' `fTree`s (`sTree_wLeaf`/`sTree_wBranch` on
  --    `pcPage`, kept by later steps through `spStep`'s page-map clause), the rest's records
  --    modulo sources, the parent's entries (`wsPutAt` at the pieces' keys: `parentSpilled`).
  --    `pieceOne_wp`'s `hbody` premise (the page size from `insSize`) needs the inodes' slice
  --    lengths, which the `wOwn` list gives (`srcOwn`'s lengths): a lemma to write.
  -- 4. the top case: `n.parent != nil && n.parent.pgid == 0` (the new parent of a split top
  --    node), `IH` (`spillIH`) on it with `spCtx .top` (`nodeRootIn` through `n`'s new parent)
  --    and its `uTree` (a branch of finished entries, the pieces spilled); its `spDone` gives
  --    `n`'s (`nodeRootIn` composed); else `return nil`.
  -- 5. the post: `spDone` from the composed steps (`StepComp`), `piecesOK`/`parentSpilled`
  --    (child) or the root's `sTree` (top).
  sorry

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
