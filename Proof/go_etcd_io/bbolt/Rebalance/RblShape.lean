/-
`txClean`'s `leafShape` through `node.rebalance`'s steps (U8e; batch 30.2): a bucket's leaf nodes
after a step hold entries of leaf nodes before (`leafFrom`: the cleared node, a removal, the
collapse, the merge), or a materialized page's (`leafShape_mat`: the page's entries of the root
shape, `rbl_matShape`, the shared fact `wOK_nodeAdded'` needs too).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblMgSel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section shape
variable [GooseExts]

/-- The leaf entries of `B'` are leaf entries of `B`. -/
def leafFrom (B B' : BRec) : Prop :=
  ∀ y ry', B'.ns !! y = some ry' → ry'.nv.isLeaf' = true → ∀ w ∈ ry'.ws,
    ∃ y0 r0, B.ns !! y0 = some r0 ∧ r0.nv.isLeaf' = true ∧ w ∈ r0.ws

theorem leafShape_bkt (X X' : WX) (bl : Loc) (B B' : BRec) (hsh : leafShape X)
    (hb : X.t.bs !! bl = some B) (hrl : X'.rl = X.rl)
    (hbs : ∀ c, X'.t.bs !! c = if c = bl then some B' else X.t.bs !! c)
    (hf : leafFrom B B') : leafShape X' := by
  intro c C hC y ry hy hleaf w hw
  rw [hrl]
  rw [hbs] at hC
  split at hC
  · rename_i hc; subst hc; cases hC
    obtain ⟨y0, r0, h0, hl0, hw0⟩ := hf y ry hy hleaf w hw
    exact hsh c B hb y0 r0 h0 hl0 w hw0
  · exact hsh c C hC y ry hy hleaf w hw

theorem setBkt_bs_if (X : WX) (bl : Loc) (B' : BRec) (c : Loc) :
    (X.setBkt bl B').t.bs !! c = if c = bl then some B' else X.t.bs !! c := by
  show (X.t.bs.insert bl B') !! c = _
  split
  · rename_i h; subst h; exact GMap.lookup_insert _ _ _
  · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)

theorem kill_bs_if (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) (c : Loc) :
    (X.kill bl B' n rn).t.bs !! c = if c = bl then some B' else X.t.bs !! c := by
  show (X.t.bs.insert bl B') !! c = _
  split
  · rename_i h; subst h; exact GMap.lookup_insert _ _ _
  · exact GMap.lookup_insert_ne _ _ (Ne.symm ‹_›)

theorem leafShape_setBkt (X : WX) (bl : Loc) (B B' : BRec) (hsh : leafShape X)
    (hb : X.t.bs !! bl = some B) (hf : leafFrom B B') : leafShape (X.setBkt bl B') :=
  leafShape_bkt X _ bl B B' hsh hb rfl (setBkt_bs_if X bl B') hf

theorem leafShape_kill (X : WX) (bl : Loc) (B B' : BRec) (n : Loc) (rn : NRec) (hsh : leafShape X)
    (hb : X.t.bs !! bl = some B) (hf : leafFrom B B') : leafShape (X.kill bl B' n rn) :=
  leafShape_bkt X _ bl B B' hsh hb rfl (kill_bs_if X bl B' n rn) hf

theorem leafFrom_start (B : BRec) (n : Loc) (rn : NRec) (hrn : B.ns !! n = some rn) :
    leafFrom B (rblStart B n rn) := by
  intro y ry' hy hl w hw
  change (<[n := rblClear rn]> B.ns) !! y = some ry' at hy
  rw [rf_lookup] at hy
  split at hy
  · rename_i h; subst h; cases hy; exact ⟨y, rn, hrn, hl, hw⟩
  · exact ⟨y, ry', hy, hl, hw⟩

theorem leafFrom_rm (B : BRec) (nl pl : Loc) (pgid : w64) (rp' : NRec)
    (hp : rp'.nv.isLeaf' = false) : leafFrom B (rmBkt B nl pl pgid rp') := by
  intro y ry' hy hl w hw
  rw [rm_ns] at hy
  split at hy
  · cases hy; rw [hp] at hl; cases hl
  split at hy
  · cases hy
  · exact ⟨y, ry', hy, hl, hw⟩

theorem leafFrom_reparent {B : BRec} {y : Loc} {ry' : NRec} {a b : Loc}
    (hy : (B.ns !! y).map
      (fun x => if x.nv.parent' = a then { x with nv := { x.nv with parent' := b } } else x) =
        some ry') (hl : ry'.nv.isLeaf' = true) (w : WEntry) (hw : w ∈ ry'.ws) :
    ∃ y0 r0, B.ns !! y0 = some r0 ∧ r0.nv.isLeaf' = true ∧ w ∈ r0.ws := by
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  refine ⟨y, ry, hry, ?_, ?_⟩
  · split at hl <;> exact hl
  · split at hw <;> exact hw

theorem leafFrom_col (B : BRec) (nl lc : Loc) (pgid : w64) (rn rc : NRec) (sI : GoSlice)
    (hrc : B.ns !! lc = some rc) : leafFrom B (colBkt B nl lc pgid (colRoot rn rc sI)) := by
  intro y ry' hy hl w hw
  rw [col_ns] at hy
  split at hy
  · cases hy; exact ⟨lc, rc, hrc, hl, hw⟩
  split at hy
  · cases hy
  · exact leafFrom_reparent hy hl w hw

theorem leafFrom_mg (B : BRec) (pl ll lr : Loc) (pgid : w64) (rp' rl rr : NRec) (moved : List Loc)
    (sI sC : GoSlice) (hp : rp'.nv.isLeaf' = false) (hrl : B.ns !! ll = some rl)
    (hrr : B.ns !! lr = some rr) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') :
    leafFrom B (mgBkt B pl ll lr pgid rp' (mgLeft rl rr moved sI sC)) := by
  intro y ry' hy hl w hw
  rw [mg_ns] at hy
  split at hy
  · cases hy; rw [hp] at hl; cases hl
  split at hy
  · cases hy
    rcases List.mem_append.1 hw with h | h
    · exact ⟨ll, rl, hrl, hl, h⟩
    · exact ⟨lr, rr, hrr, by rw [← hkind]; exact hl, h⟩
  split at hy
  · cases hy
  · exact leafFrom_reparent hy hl w hw

/-- **A materialized page's leaf entries are of the root shape** (shared gap, batch 30.2: the
statement `wOK_nodeAdded'`'s callers need too, U7d): a page at a position of the bucket `bl` is in
the root bucket's tree iff `bl` is the root bucket, and `rootShape` gives its leaves' flags. Not
proved here: the writer's records do not say which buckets' pages are top-level (it needs a
nesting-depth fact for each bucket's root page). -/
theorem rbl_matShape (X X' : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (l : Loc) (pgid : w64)
    (p : Loc) (i : Nat) (hI : rblX X fl bl dfc) (h : nodeAdded X X' bl l pgid p)
    (hpos : ∃ B, X.t.bs !! bl = some B ∧ pagePosAt B p i pgid) :
    ∀ B' r, X'.t.bs !! bl = some B' → B'.ns !! l = some r → r.nv.isLeaf' = true →
      ∀ w ∈ r.ws, (isBktFlag w.flags ↔ bl = X.rl) := by
  sorry

/-- **`leafShape` through a branch's child materialized** (`rblX_sibMat`'s step). -/
theorem leafShape_sibMat (X1 X2 : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B1 : BRec)
    (p : Loc) (r1 : NRec) (i : Nat) (w0 : WEntry) (lc : Loc) (hsh : leafShape X1)
    (hI : rblX X1 fl bl dfc) (hb : X1.t.bs !! bl = some B1) (hr : B1.ns !! p = some r1)
    (hbr : r1.nv.isLeaf' = false) (hw : r1.ws[i]? = some w0)
    (hmat : (B1.nm !! w0.pgid = some lc ∧ X2 = X1) ∨ nodeAdded X1 X2 bl lc w0.pgid p) :
    leafShape X2 := by
  rcases hmat with ⟨-, rfl⟩ | hadd
  · exact hsh
  have hpos : ∃ B, X1.t.bs !! bl = some B ∧ pagePosAt B p i w0.pgid := by
    have hnone : B1.nm !! w0.pgid = none := by
      obtain ⟨B0, -, -, -, -, -, hB0, -, hnone, -⟩ := hadd
      rw [hb] at hB0; cases hB0; exact hnone
    exact ⟨B1, hb, r1, w0, hr, hbr, hw, rfl, hnone⟩
  have hshape := rbl_matShape X1 X2 fl bl dfc lc w0.pgid p i hI hadd hpos
  have hadd' := hadd
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd'
  rw [hb] at hB0; cases hB0
  have hlo : B1.ns !! lc = none := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hobj, -⟩ := hadd
    cases hl' : B1.ns !! lc with
    | none => rfl
    | some _ =>
      have := (objs_isSome X1.t lc).2 (Or.inr ⟨bl, B1, hb, by rw [hl']; rfl⟩)
      rw [Option.isNone_iff_eq_none] at hobj; rw [hobj] at this; cases this
  subst hX'
  rcases hcase with ⟨hpn, -, rfl⟩ | ⟨-, -, rp0, rp', hrp0, -, -, hc2, -, hc4, -, -, hc6, rfl⟩
  · exact Write.leafShape_matX X1 bl lc w0.pgid B1 _ r hsh hb (GMap.lookup_insert _ _ _)
      (fun y ry' hy => by
        by_cases hyl : y = lc
        · exact Or.inl hyl
        · right
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
          exact ⟨ry', hy, rfl, rfl, rfl, rfl⟩)
      (fun hl w hw' => hshape _ r (GMap.lookup_insert _ _ _) (GMap.lookup_insert _ _ _) hl w hw')
  · rw [hr] at hrp0; cases hrp0
    exact Write.leafShape_matX X1 bl lc w0.pgid B1 _ r hsh hb (GMap.lookup_insert _ _ _)
      (fun y ry' hy => by
        by_cases hyl : y = lc
        · exact Or.inl hyl
        · right
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
          by_cases hyp : y = p
          · subst hyp
            rw [GMap.lookup_insert] at hy; cases hy
            exact ⟨r1, hr, by rw [hc6], hc2, by rw [hc6], hc4⟩
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyp)] at hy
            exact ⟨ry', hy, rfl, rfl, rfl, rfl⟩)
      (fun hl w hw' => hshape _ r (GMap.lookup_insert _ _ _) (GMap.lookup_insert _ _ _) hl w hw')

end shape

end bbolt
end EtcdGrove
end Perennial
