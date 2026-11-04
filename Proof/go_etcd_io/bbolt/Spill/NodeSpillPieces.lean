/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **`spillTail_wp`**,
the WP of `Spill/NodeSpillPiecesCode`'s `spillTail` (`n.children = nil`, the split, the pieces'
loop, the top case's recursion) from the state after the loop (`spEnd`) to `n`'s spill's post
(`spPost`), over Löb's hypothesis `spillIH` (the top case's `n.parent.spill()`). U9s: the heap steps are
`Spill/NodeSpillTailWp.spillTail_gen`'s, over the pieces' loop's invariant `pcInv` and its pure
facts (`Spill/NodeSpillTailInv`).

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
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailWp
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitPcPre
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitMain
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStep
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailTopMain

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
  -- U9s: `Spill/NodeSpillTailWp.spillTail_gen` (the heap steps, proved) over the pieces' loop's
  -- invariant `Spill/NodeSpillTailInv.pcInv` and its pure facts.
  obtain ⟨hn', hlv', hS⟩ := tail_pre hpre hsp hend
  exact spillTail_gen hAlloc hPage hSplit hWrite hPut hSize hInc hTxid hPgid hId hKey hAssert hFree
    K tx r m X w bl n rn O lo hi h D N E cs X' w' r' st np txp resp e0
    (pcInv X w bl n rn O lo hi h D N E cs) hn' hlv' (tail_wsLive hpre hsp hend) hS
    (fun hl hd => pcInv_init' hpre hsp hend hl hd)
    (pcInv_pre' hpre hsp) (pcInv_stepX hpre hsp) pcInv_err pcInv_end (pcInv_doneX hpre hsp)
    (pcInv_topX hpre hsp)

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
