/-
Pure facts `node.rebalance`'s WP proof uses (U8b, `notes/bbolt-proof-plan.md`): the search index
of an entry's own key in sorted entries (`node.del` of a child's key), the writer's txid from
the invariant and the database side, and the size bound `node.size`'s spec takes.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.HeapRblKill
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem WX.setBkt_v (X : WX) (bl : Loc) (B : BRec) : (X.setBkt bl B).v = X.v := rfl
theorem WX.setBkt_handles (X : WX) (bl : Loc) (B : BRec) :
    (X.setBkt bl B).handles = X.handles := rfl
theorem WX.setBkt_nloc (X : WX) (bl : Loc) (B : BRec) : (X.setBkt bl B).nloc = X.nloc := rfl
theorem WX.kill_v (X : WX) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) :
    (X.kill bl B n r).v = X.v := rfl
theorem WX.kill_handles (X : WX) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) :
    (X.kill bl B n r).handles = X.handles := rfl
theorem WX.kill_nloc (X : WX) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) :
    (X.kill bl B n r).nloc = X.nloc := rfl

theorem WX.setNode_v (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).v = X.v := by
  unfold WX.setNode; split <;> rfl
theorem WX.setNode_handles (X : WX) (bl l : Loc) (r : NRec) :
    (X.setNode bl l r).handles = X.handles := by
  unfold WX.setNode; split <;> rfl
theorem WX.setNode_nloc (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).nloc = X.nloc := by
  unfold WX.setNode; split <;> rfl
theorem WDb.withFl_withFl (w : WDb) (a b : FLPg) : (w.withFl a).withFl b = w.withFl b := rfl

/-- In sorted entries, an entry's key searches to its index. -/
theorem wsIdx_at (ws : List WEntry) (i : Nat) (w : WEntry) (hs : wsSorted ws)
    (hw : ws[i]? = some w) : wsIdx ws w.key = i := by
  have hi := (List.getElem?_eq_some_iff.1 hw).1
  have hk : wKey ws i = w.key := by unfold wKey; rw [hw]; rfl
  apply Write.wsIdx_of_bounds ws w.key i (by omega)
  · intro k hk'
    rw [← hk]; exact hs k i hk' hi
  · intro _; rw [hk]; exact go.goStringLt_irrefl _

/-- `del` of an entry's own key in sorted entries: found, and the entry removed. -/
theorem wsDelAt_at (ws : List WEntry) (i : Nat) (w : WEntry) (hs : wsSorted ws)
    (hw : ws[i]? = some w) : wsFound ws w.key ∧ wsDelAt ws w.key = ws.eraseIdx i := by
  have hidx := wsIdx_at ws i w hs hw
  have hf : wsFound ws w.key := by
    unfold wsFound; rw [hidx, hw]; rfl
  refine ⟨hf, ?_⟩
  unfold wsDelAt
  rw [if_pos hf, hidx, List.eraseIdx_eq_take_drop_succ]

/-- A node of a bucket that is not inline was read from a page of the view (`treeWF`). -/
theorem rbl_node_page (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hI : rblX X fl dbl dfc) (hb : X.t.bs !! bl = some B)
    (hr : B.ns !! n = some r) (hroot : B.ib.root' ≠ W64 0) :
    ∃ pg, X.v.pages !! r.nv.pgid'.toNat = some pg ∧ r.nv.pgid' ≠ W64 0 := by
  have hc := (hI.2.1 bl B hb).1.1
  have hwf := (hc.2.2.2.2.2.2.2.1 n r hr).2.2.2.2.2.2.2.2.2.1 hroot
  rcases hwf with ⟨_, pg, h2, _, hpg, _, _, _⟩
  refine ⟨pg, hpg, fun h => ?_⟩
  rw [h] at h2; simp at h2

/-- A branch's bucket is not inline (an inline bucket's nodes are leaves). -/
theorem rbl_root_ne (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hI : rblX X fl dbl dfc) (hb : X.t.bs !! bl = some B)
    (hr : B.ns !! n = some r) (hbr : r.nv.isLeaf' = false) : B.ib.root' ≠ W64 0 := by
  intro h0
  have := (hI.2.1 bl B hb).1.1.2.2.2.2.2.2.1 h0 n r hr
  rw [hbr] at this; cases this

/-- **A node's page size fits an `int`** (`node.size`'s premise). A `sorry`: nothing in `rblX`
bounds a node's number of entries or their sizes (see the U8b report). -/
theorem rblX_insSize (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hI : rblX X fl dbl dfc) (hb : X.t.bs !! bl = some B)
    (hr : B.ns !! n = some r) : insSize r.ins < 2 ^ 63 := by
  sorry

/-- The writer's txid (`tx.meta.txid`) is the database side's `wtxid`. -/
theorem rblX_wtxid (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (w : WDb)
    (hI : rblX X fl dbl dfc) (hv : X.v = View.ofC X.v.base w.C) : X.t.mv.txid' = w.wtxid := by
  have h := hI.1.2.2.2.1
  have hv' : X.v.txid = w.C.txid := by rw [hv]; rfl
  unfold WDb.wtxid
  apply BitVec.eq_of_toNat_eq
  rw [← h, hv']
  have hlt : w.C.txid + 1 < 2 ^ 64 := by
    have := X.t.mv.txid'.isLt; rw [← h, hv'] at this; exact this
  simp only [BitVec.toNat_ofInt]
  omega

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer's working state, split (without unfolding `wtxW` elsewhere in a goal). -/
theorem wtxW_split (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊣⊢ iprop(wtxCore K tx r m X ∗ viewCells wq X.v ∗
      ∃ l : Nat, mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, l) : MapSt) ∗
        ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝) := by
  unfold wtxW; exact .rfl

/-- A live node's object, unfolded. -/
theorem objOwn_live_node (v : View) (l : Loc) (dq : DFrac) (bl : Loc) (r : NRec) :
    objOwn (GF := GF) v l dq true (.node bl r) ⊣⊢ iprop(
      l ↦{dq} r.nv ∗ r.nv.inodes' ↦*{dq} r.ins ∗
      (if r.capOwn then ownSliceCap Inode r.nv.inodes' dq else emp) ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn v true it w) ∗
      r.nv.children' ↦*{dq} r.cs ∗ ownSliceCap Loc r.nv.children' dq ∗
      (if true ∧ r.nv.key' ≠ slice.nil then srcOwn v r.nv.key' r.ksrc r.key else emp)) := by
  unfold objOwn; exact .rfl

/-- A bucket's page fact depends on its `page` field and inline page only. -/
theorem pageOwn_congr' (v : View) (B B' : BRec) (h1 : B'.bv = B.bv) (h5 : B'.ipg = B.ipg)
    (h6 : B'.isrc = B.isrc) (h7 : B'.pst = B.pst) : pageOwn (GF := GF) v B' = pageOwn v B := by
  simp only [pageOwn, h1, h5, h6, h7]

/-- A bucket's object, unfolded. -/
theorem objOwn_bkt_unf (v : View) (l : Loc) (dq : DFrac) (b : Bool) (B : BRec) :
    objOwn (GF := GF) v l dq b (.bkt B) ⊣⊢ iprop(
      l.[Bucket, go!"InBucket"] ↦{dq} B.bv.InBucket' ∗
      (if l = B.bv.tx'.[Tx, go!"root"] then l.[Bucket, go!"tx"] ↦{dq} B.bv.tx'
       else l.[Bucket, go!"tx"] ↦□ B.bv.tx') ∗
      l.[Bucket, go!"buckets"] ↦{dq} B.bv.buckets' ∗ l.[Bucket, go!"page"] ↦{dq} B.bv.page' ∗
      l.[Bucket, go!"rootNode"] ↦{dq} B.bv.rootNode' ∗ l.[Bucket, go!"nodes"] ↦{dq} B.bv.nodes' ∗
      B.bv.InBucket' ↦{dq} B.ib ∗ B.bv.nodes' ↦${dq} B.nm ∗ B.bv.buckets' ↦${dq} B.bm ∗
      (if b then pageOwn v B else emp)) := by
  unfold objOwn; exact .rfl

open Iris.BI Iris.ProofMode in
/-- The writer's view is the committed state's (`wdbW`'s fact, kept). -/
theorem wdbW_view_rbl (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜v = View.ofC v.base w.C⌝ ∗ wdbW K tx v w := by
  unfold wdbW
  iintro ⟨H, %Hw⟩
  isplitr
  · ipureintro; exact Hw.2.2
  iframe; ipureintro; exact Hw

open Iris.BI Iris.ProofMode in
/-- A bucket's node cache is not nil (its map points-to). -/
theorem nodes_nonnull (l : Loc) (dq : DFrac) (m : GMap w64 Loc) :
    (l ↦${dq} m : IProp GF) ⊢ ⌜l ≠ null⌝ ∗ l ↦${dq} m := by
  rw [ownMap_unseal]
  iintro Hm
  iNamed Hm
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hown
  isplitr
  · ipureintro; exact Hnn
  unfold ownMapDef
  iexists _, _
  iframe
  ipureintro; exact Hrepr

/-- The database's core is persistent. -/
instance BC_core_persistent_rbl (K : BC) : Iris.BI.Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

open Iris.BI Iris.ProofMode in
/-- The database's page size (`db.pageSize`, persistent in the core). -/
theorem rbl_pageSize (K : BC) : K.core (GF := GF) ⊢ K.db.[DB, go!"pageSize"] ↦□ W64 4096 := by
  unfold BC.core isBoltCoreP dbFixed
  iintro ⟨-, -, -, -, -, ⟨H, -⟩, -⟩
  iexact H

end heap

end bbolt
end EtcdGrove
end Perennial
