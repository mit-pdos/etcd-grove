/-
The root's only child materialized before the collapse (`n.bucket.node(n.inodes[0].Pgid(), n)` in
`node.rebalance`, U8d): from `Bucket.node`'s postcondition (cached, or `nodeAdded`), the bucket after
with the child's record, the invariant kept (`rblX_mat`), and the root's record after (its children
slice may have grown).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section colmat
variable [GooseExts]

/-- **The root's child materialized** (`Bucket.node` of the root `n`'s only entry `w0`). -/
theorem rblX_colMat (X1 X2 : WX) (fl : FLPg) (bl : Loc) (B1 : BRec) (n : Loc) (r1 : NRec)
    (w0 : WEntry) (lc : Loc)
    (hI : rblX X1 fl bl (some n)) (hb : X1.t.bs !! bl = some B1) (hr : B1.ns !! n = some r1)
    (hbr : r1.nv.isLeaf' = false) (hws : r1.ws = [w0])
    (hmat : (B1.nm !! w0.pgid = some lc ∧ X2 = X1) ∨ nodeAdded X1 X2 bl lc w0.pgid n)
    (hnl : (X1.t.objs !! lc).isNone → X1.nloc !! lc = none) :
    ∃ B2 r2 rc, X2.t.bs !! bl = some B2 ∧ B2.ns !! n = some r2 ∧ B2.nm !! w0.pgid = some lc ∧
      B2.ns !! lc = some rc ∧ rblX X2 fl bl (some n) ∧ rblRel X1 fl X2 fl X1.t.mv.txid' ∧
      (∀ bl', bl' ≠ bl → X2.t.bs !! bl' = X1.t.bs !! bl') ∧
      r2.nv = { r1.nv with children' := r2.nv.children' } ∧ r2.ws = r1.ws ∧ r2.ins = r1.ins ∧
      r2.key = r1.key ∧ r2.ksrc = r1.ksrc ∧ r2.capOwn = r1.capOwn ∧
      (∀ y ry', B2.ns !! y = some ry' → ry'.nv.unbalanced' = true →
        ∃ ry, B1.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  have hB := (hI.2.1 bl B1 hb).1
  rw [if_pos rfl] at hB
  have hc := hB.1
  rcases hmat with ⟨hlc, rfl⟩ | hadd
  · obtain ⟨-, rc, hrc, -⟩ := hc.2.2.2.2.1 _ _ hlc
    exact ⟨B1, r1, rc, hb, hr, hlc, hrc, hI, rblRel_refl _ _ _, fun _ _ => rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, fun y ry' hy hu => ⟨ry', hy, hu, rfl⟩⟩
  have hadd' := hadd
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, -, hnone, -, hobj, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd'
  rw [hb] at hB0; cases hB0
  have hpos : ∃ B, X1.t.bs !! bl = some B ∧ pagePosAt B n 0 w0.pgid :=
    ⟨B1, hb, r1, w0, hr, hbr, by rw [hws]; rfl, rfl, hnone⟩
  obtain ⟨hI2, hR2, hU2⟩ := rblX_mat X1 X2 fl bl (some n) lc w0.pgid n 0 hI hadd hpos (hnl hobj)
  have hnn : n ≠ null := (hc.2.2.2.2.1 _ _ (ncol_nm (hc.2.2.2.2.2.2.2.1 n r1 hr))).1
  have hlcn : lc ≠ n := by
    intro he; subst he
    have := (objs_isSome X1.t lc).2 (Or.inr ⟨bl, B1, hb, by rw [hr]; rfl⟩)
    rw [Option.isNone_iff_eq_none] at hobj; rw [hobj] at this; cases this
  rcases hcase with ⟨hpn, -, -⟩ | ⟨-, hbv, rp0, rp', hrp0, -, hc1, hc2, hc3, hc4, hc5, hcp, hc6, hns⟩
  · exact absurd hpn hnn
  rw [hr] at hrp0; cases hrp0
  subst hbv; subst hns
  have hb2 : X2.t.bs !! bl =
      some { B1 with nm := B1.nm.insert w0.pgid lc, ns := (B1.ns.insert n rp').insert lc r } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  refine ⟨_, rp', r, hb2, ?_, GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _, hI2, hR2, ?_, hc6,
    hc2, hc3, hc4, hc5, hcp, hU2 B1 _ hb hb2⟩
  · show ((B1.ns.insert n rp').insert lc r) !! n = _
    rw [GMap.lookup_insert_ne _ _ hlcn]; exact GMap.lookup_insert _ _ _
  · intro bl' hne
    rw [hX']; exact GMap.lookup_insert_ne _ _ (Ne.symm hne)

end colmat

end bbolt
end EtcdGrove
end Perennial
