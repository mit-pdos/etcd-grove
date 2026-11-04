/-
`node.rebalance`'s steps over the writer's records (U8b, `notes/bbolt-proof-plan.md`): each keeps
`rebalance`'s invariant `rblX` (`Rebalance/RblX.lean`) and extends `rblRel`, lifting the bucket's
steps (`Rebalance/RblStart`, `RblRm`, `RblCol`, `RblMg*`: `rblB`) to the transaction (the logical
trees through `Rebalance/RTreeSteps`, the freelist agreement `flView`, the registry, the live
objects reached). A removed node goes dead (`WX.kill`), its page's extent freed.

Every lemma is about the records after all of a step's code (the WP proof of `node.rebalance`
tracks the heap through the step and ends there):
- `rblX_init`: at `Commit`, from `wOK` (the premises the spec has, and `covU`, `nsLive`);
- `rblX_start` / `rblX_done`: the node's `unbalanced` cleared; done if big enough or a root;
- `rblX_mat`: a sibling or the root's child materialized (`nodeAdded`);
- `rblX_canFree`: a live node's page can be freed (`node.free`'s premises);
- `rblX_rm`: an empty leaf removed from its parent;
- `rblX_col`: the root collapsed into its only child.
(The merge, `rblX_mg`, is over `Rebalance/RblMg*`.)
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblX
public import Proof.go_etcd_io.bbolt.Rebalance.RblRm
public import Proof.go_etcd_io.bbolt.Rebalance.RblCol
public import Proof.go_etcd_io.bbolt.Rebalance.RblReady
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSSim
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSFree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]

/-- `X` with bucket `bl`'s record `B'` (without the node `n`) and `n` dead (its record `rn`). -/
def WX.kill (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl B', dead := X.t.dead.insert n (.node bl rn) },
           live := X.live.delete n }

/-- Every node of every bucket is live (before `Commit`, no node of a bucket is dead). -/
def nsLive (X : WX) : Prop :=
  ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live

/-- **At `Commit`, the invariant** (no deficient node). -/
theorem rblX_init (X : WX) (fl : FLPg) (dbl : Loc) (hok : wOK X) (hr : liveReach X)
    (hfl : flView X fl) (hu : covU X) (hl : nsLive X)
    (hext : ∀ id pg, X.v.pages !! id = some pg → id + (1 + pageOverflow pg) ≤ 2 ^ 62)
    (hlen : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length)
    (hod : objsDisj X.t) (hrh : ∀ bl, (X.t.bs !! bl).isSome → bl = X.rl ∨ (X.handles !! bl).isSome) :
    rblX X fl dbl none := by
  have hok' := hok
  obtain ⟨⟨htw, hpm, hhwm, htx, hrl, hcl⟩, hkn, -, hEB, hH, hL, hN, hV⟩ := hok'
  refine ⟨⟨htw, hpm, hhwm, htx, hrl⟩, fun bl B hb => ?_, hEB, hH, hL, hN, hV, hr, hfl, hu, hext, hlen,
    hod, hrh⟩
  refine ⟨by rw [ite_self]; exact rblB_of_wOK X hok bl B hb, (hcl bl B hb).2, (hkn bl B hb).2,
    rtOK_init X bl hok hV (by rw [hb]; rfl), fun l r hr => hl bl B l r hb hr⟩

/-- **The node's `unbalanced` cleared** (`n.unbalanced = false`): the node is the deficient
one. -/
theorem rblX_start (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (n : Loc)
    (r : NRec) (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hd : dfc = none ∨ dfc = some n) :
    rblX (X.setBkt bl (rblStart B n r)) fl bl (some n) ∧
      rblRel X fl (X.setBkt bl (rblStart B n r)) fl X.t.mv.txid' := by
  have hB := (hI.2.1 bl B hb).1
  rw [if_pos rfl] at hB
  have hs := bktSim_set B n r (rblClear r) hr (nrecEq_clear r)
  exact rblX_sim X fl bl dfc (some n) B _ _ hI hb hs (rblB_start _ _ bl B n r dfc hB hr hd)
    (fun k v h => entryIn_sim _ hs k v h)

/-- **Done** (the node big enough, or a root not collapsed): no deficient node. -/
theorem rblX_done (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (n : Loc)
    (r : NRec) (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hd : dfc = none ∨ dfc = some n)
    (h2 : r.nv.isLeaf' = false → 2 ≤ r.ws.length)
    (h1 : r.nv.isLeaf' = true → r.nv.parent' ≠ null → 0 < r.ws.length) :
    rblX (X.setBkt bl (rblStart B n r)) fl bl none ∧
      rblRel X fl (X.setBkt bl (rblStart B n r)) fl X.t.mv.txid' ∧
      rblStep B (rblStart B n r) n := by
  have hB := (hI.2.1 bl B hb).1
  rw [if_pos rfl] at hB
  have hs := bktSim_set B n r (rblClear r) hr (nrecEq_clear r)
  obtain ⟨hB', hst, hent⟩ := rbl_done _ _ bl B n r dfc hB hr hd h2 h1
  obtain ⟨h1, h2⟩ := rblX_sim X fl bl dfc none B _ X.t.mv.txid' hI hb hs hB' hent
  exact ⟨h1, h2, hst⟩

/-- **A sibling, or the root's only child, materialized** (`b.node` of the parent's entry `i`, a
page position). The new node is not unbalanced. -/
theorem rblX_mat (X X' : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (l : Loc) (pgid : w64)
    (parent : Loc) (i : Nat) (hI : rblX X fl bl dfc) (h : nodeAdded X X' bl l pgid parent)
    (hpos : ∃ B, X.t.bs !! bl = some B ∧ pagePosAt B parent i pgid) :
    rblX X' fl bl dfc ∧ rblRel X fl X' fl X.t.mv.txid' ∧
      ∀ B B', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → ∀ y ry', B'.ns !! y = some ry' →
        ry'.nv.unbalanced' = true → B.ns !! y = some ry' := by
  sorry

/-- **A live node's page can be freed** (`node.free`'s premises: the page of the view, its
header, and `Free`'s `canFree` for the writer's txid). -/
theorem rblX_canFree (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (n : Loc)
    (r : NRec) (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hp0 : r.nv.pgid' ≠ W64 0) :
    ∃ pg, X.v.pages !! r.nv.pgid'.toNat = some pg ∧ 16 ≤ pg.length ∧
      pageId pg = r.nv.pgid'.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      fl.canFree X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg) :=
  rblX_canFree' X fl bl dfc B n r hI hb hr hp0

/-- **An empty leaf removed** from its parent `pl` (entry `i`; `del`, `removeChild`, the node
cache's entry deleted, `free`): the parent is the deficient node. -/
theorem rblX_rm (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (pl : Loc)
    (rp : NRec) (i : Nat) (w : WEntry) (sI sC : GoSlice) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hleaf : r.nv.isLeaf' = true) (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null)
    (hrp : B.ns !! pl = some rp) (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid')
    (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) bl (some pl) ∧
    rblRel X fl (X.kill bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    r.nv.pgid' ≠ W64 0 ∧ 2 ≤ rp.ws.length := by
  sorry

/-- **The root collapsed into its only child** `lc` (materialized; its record `rc`): the child
dead with its parent nil and its page freed; no deficient node. -/
theorem rblX_col (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (w0 : WEntry)
    (lc : Loc) (rc : NRec) (sI : GoSlice) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hrn : B.ns !! n = some rn)
    (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
    (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc)
    (hpg : X.v.pages !! rc.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)) lc
        { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' rc.nv.pgid' (1 + pageOverflow pg)) bl none ∧
    rblRel X fl (X.kill bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)) lc
        { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' rc.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    rc.nv.pgid' ≠ W64 0 ∧
    (∀ y ry', (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry' →
        ry'.nv.unbalanced' = true → y = n ∧ rn.nv.unbalanced' = true ∨
        (y ≠ lc ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
          ry'.nv.pgid' = ry.nv.pgid')) := by
  sorry

end steps

end bbolt
end EtcdGrove
end Perennial
