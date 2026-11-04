/-
The writer's logical trees as finite trees (U8b, `notes/bbolt-proof-plan.md`): `rtOK X bl`, a
finite tree of bucket `bl`'s logical tree from its root position, of height below the walks'
fuel, its leaves at one depth. At `Commit` every bucket has one (`rtOK_init`: from `wOK` and the
view's page heights, `viewWF`: before `Commit` the logical tree has its pages' shape, `txPg`).
It gives the walks (`leaves_rt`, `positions_rt`, `leafDepthOK_rt`). The records locate the
changed positions (`edge_mat`, `root_mat`: a materialized node occurs only under its parent's
position, the root node at the root), and a change of a bucket's records off some positions
keeps `ltree` there (`ltree_frame`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeSteps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rtx
variable [GooseExts]

/-- **Bucket `bl`'s logical tree is finite** (see the module doc). -/
def rtOK (X : WX) (bl : Loc) : Prop :=
  ∃ t, ltIs (ltree X) bl t ∧ t.pid = X.rootPid bl ∧ t.ht < X.fuel ∧ ∃ D, ∀ x ∈ t.dps 0, x = D

/-- **At `Commit`, every bucket's logical tree is finite**, its leaves at one depth (the root
page's height: before `Commit` a branch node's entries are its page's, `txPg`). -/
theorem rtOK_init (X : WX) (bl : Loc) (hok : wOK X) (hv : viewWF X.v)
    (hb : (X.t.bs !! bl).isSome) : rtOK X bl := by
  sorry

theorem leaves_rt (X : WX) (bl : Loc) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) (hh : t.ht < X.fuel) : X.leaves bl = t.lvs := by
  unfold WX.leaves; rw [← hp]; exact lleaves_ltIs (ltree X) bl t X.fuel ht hh

theorem positions_rt (X : WX) (bl : Loc) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) (hh : t.ht < X.fuel) : X.positions bl = t.pos := by
  unfold WX.positions; rw [← hp]; exact lposF_ltIs (ltree X) bl t X.fuel ht hh

theorem leafDepthOK_rt (X : WX) (bl : Loc) (h : rtOK X bl) : leafDepthOK X bl := by
  obtain ⟨t, ht, hp, hh, D, hD⟩ := h
  refine ⟨D, ?_⟩
  rw [← hp, ldepthsF_ltIs (ltree X) bl t X.fuel 0 ht hh]
  exact hD

/-- **A materialized child occurs only under its parent's position** (`nodeClean`'s parent and
child clauses; below an unmaterialized position only pages, `posNodeFree`). -/
theorem edge_mat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (t : RTree) (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) :
    ∀ x c, t.edge x c → ∀ l r, B.nm !! c = some l → B.ns !! l = some r →
      B.nm !! x = some r.nv.parent' := by
  sorry

/-- **The root position holds the root node** (if materialized): a materialized node at the
root has no parent. -/
theorem root_mat (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (l : Loc) (r : NRec) (hl : B.nm !! X.rootPid bl = some l) (hr : B.ns !! l = some r) :
    r.nv.parent' = null := by
  sorry

/-- The kind and entries of a node record (what `ltree` reads). -/
def NRec.kw (r : NRec) : Bool × List WEntry := (r.nv.isLeaf', r.ws)

/-- **`ltree` is kept off the changed positions `S`**: bucket `bl`'s record changed to `B'` with
its header, root node and node cache kept off `S`, and each node cached off `S` with its kind
and entries; the other buckets and the view kept. -/
theorem ltree_frame (X X' : WX) (bl : Loc) (B B' : BRec) (S : w64 → Prop)
    (hb : X.t.bs !! bl = some B) (hb' : X'.t.bs !! bl = some B')
    (hother : ∀ bl', bl' ≠ bl → X'.t.bs !! bl' = X.t.bs !! bl') (hv : X'.v = X.v)
    (hib : B'.ib = B.ib) (hrn : B'.bv.rootNode' = B.bv.rootNode') (hpg : B'.bv.page' = B.bv.page')
    (hipg : B'.ipg = B.ipg)
    (hnm : ∀ q, ¬ S q → B'.nm !! q = B.nm !! q)
    (hns : ∀ q l, ¬ S q → B.nm !! q = some l → (B'.ns !! l).map NRec.kw = (B.ns !! l).map NRec.kw)
    (hinl : B.ib.root' = W64 0 → (B'.ns !! B.bv.rootNode').map NRec.kw =
      (B.ns !! B.bv.rootNode').map NRec.kw) :
    ∀ bl' q, (bl' = bl → ¬ S q) → ltree X' bl' q = ltree X bl' q := by
  sorry

/-- The walks' fuel is kept when the view and the buckets' locations are. -/
theorem fuel_eq (X X' : WX) (hv : X'.v.pages = X.v.pages)
    (hbs : ∀ bl, (X'.t.bs !! bl).isSome = (X.t.bs !! bl).isSome) : X'.fuel = X.fuel := by
  sorry

end rtx

end bbolt
end EtcdGrove
end Perennial
