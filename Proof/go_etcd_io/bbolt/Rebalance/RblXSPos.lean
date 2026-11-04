/-
A live node's page is a position of its bucket's logical tree (U8b, `Rebalance/RblXSteps.lean`):
the node descends from the root node (`liveReach`), which sits at the root position, and a child
node sits at an entry of its parent, whose position's entries are the parent's (`node_pos`); its
extent is its page's (`posExtent_node`), so its slots are covered (`lCovers_node`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pos
variable [GooseExts]

open RTree in
theorem ltIsL_pid (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → ∀ w ∈ ws, ∃ c ∈ cs, c.pid = w.pgid
  | [], [], _, w, hw => by simp at hw
  | x :: ws, t :: ts, h, w, hw => by
    simp only [ltIsL] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨t, List.mem_cons_self, h.1⟩
    · obtain ⟨c, hc, he⟩ := ltIsL_pid L bl ws ts h.2.2 w hw
      exact ⟨c, List.mem_cons_of_mem _ hc, he⟩
  | [], _ :: _, h, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _, _ => by simp only [ltIsL] at h

open RTree in
/-- **A branch position's entries are positions.** -/
theorem pos_child (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (x : w64) (hx : x ∈ t.pos)
    (ws : List WEntry) (hL : L bl x = some (false, ws)) (w : WEntry) (hw : w ∈ ws) :
    w.pgid ∈ t.pos := by
  obtain ⟨s, hs, hsp⟩ := pos_subs t x hx
  have hsl := ltIs_subs L bl t s ht hs
  obtain ⟨cs, rfl, -, hcs⟩ := ltIs_node L bl s x false ws hsl hsp hL
  obtain ⟨c, hc, hcp⟩ := ltIsL_pid L bl ws cs (hcs rfl) w hw
  rw [← hcp]
  exact subs_pid_pos L bl t c ht (subs_trans t _ hs c (child_mem_subs x false ws cs c hc c
    (self_mem_subs c)))

/-- The logical tree at a node's page id is the node (a bucket with a root page). -/
theorem ltree_node (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0) (a : Loc) (ra : NRec)
    (ha : B.ns !! a = some ra) : ltree X bl ra.nv.pgid' = some (ra.nv.isLeaf', ra.ws) := by
  have hnm : B.nm !! ra.nv.pgid' = some a := (hc.2.2.2.2.2.2.2.1 a ra ha).2.2.2.2.2.2.2.1
  unfold ltree
  rw [hb]
  simp only [resolve, if_neg h0, hnm, ha, Option.map_some]

/-- The resolved node at a node's page id is the node. -/
theorem resolve_node (B : BRec) (v : View) (hwm : Nat) (bl : Loc) (hc : bktClean v hwm bl B)
    (h0 : B.ib.root' ≠ W64 0) (a : Loc) (ra : NRec) (ha : B.ns !! a = some ra) :
    resolve B ra.nv.pgid' = some a := by
  have hnm : B.nm !! ra.nv.pgid' = some a := (hc.2.2.2.2.2.2.2.1 a ra ha).2.2.2.2.2.2.2.1
  simp only [resolve, if_neg h0, hnm]

/-- **A node reached from the root node is at a position.** -/
theorem node_pos (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (hrt : rtOK X bl) (h0 : B.ib.root' ≠ W64 0) (rt n : Loc)
    (hrtI : nodeRootIn B B.bv.rootNode' rt) (hd : descIn B rt n) (r : NRec)
    (hr : B.ns !! n = some r) : r.nv.pgid' ∈ X.positions bl := by
  obtain ⟨t, ht, hp, hh, -⟩ := hrt
  rw [positions_rt X bl t ht hp hh]
  -- the root
  have hrt_eq : ∃ rr, rt = B.bv.rootNode' ∧ B.ns !! rt = some rr := by
    cases hrtI with
    | top _ rr hrr _ => exact ⟨rr, rfl, hrr⟩
    | up _ _ rr hrr hp' _ => exact absurd (hroot rr hrr) hp'
  obtain ⟨rr, hrte, hrr⟩ := hrt_eq
  have hrrpos : rr.nv.pgid' ∈ t.pos := by
    have hnn : B.bv.rootNode' ≠ null := by
      intro he
      have := (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 rt rr hrr).2.2.2.2.2.2.2.1).1
      rw [hrte, he] at this; exact this rfl
    have hnm := hc.2.2.2.1 hnn
    obtain ⟨-, r1, h1, p1⟩ := hc.2.2.2.2.1 _ _ hnm
    rw [← hrte, hrr] at h1; cases h1
    rw [p1]
    have : t.pid = B.ib.root' := by rw [hp]; simp [WX.rootPid, hb]
    rw [← this, pos_eq _ _ t ht]
    exact List.mem_cons_self
  -- down the children
  have key : ∀ a d, descIn B a d → ∀ ra, B.ns !! a = some ra → ra.nv.pgid' ∈ t.pos →
      ∀ rd, B.ns !! d = some rd → rd.nv.pgid' ∈ t.pos := by
    intro a d h
    induction h with
    | self n => intro ra ha hpa rd hd; rw [ha] at hd; cases hd; exact hpa
    | child a c d ra0 ha0 hcin _ ih =>
      intro ra ha hpa rd hdd
      rw [ha0] at ha; cases ha
      have hna := hc.2.2.2.2.2.2.2.1 a ra0 ha0
      obtain ⟨rc, hrc, hpc⟩ := hna.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hcin
      have hnc := hc.2.2.2.2.2.2.2.1 c rc hrc
      have hann : a ≠ null := (hc.2.2.2.2.1 _ _ hna.2.2.2.2.2.2.2.1).1
      obtain ⟨rp, hrp, hbr, -, w, hw, hwp⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by rw [hpc]; exact hann)
      rw [hpc, ha0] at hrp; cases hrp
      have hL := ltree_node X bl B hb hc h0 a ra0 ha0
      rw [hbr] at hL
      have := pos_child (ltree X) bl t ht _ hpa _ hL w hw
      rw [hwp] at this
      exact ih rc hrc this rd hdd
  exact key rt n hd rr hrr hrrpos r hr

/-- **A node's extent is its page's.** -/
theorem posExtent_node (X : WX) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' ≠ W64 0) (n : Loc) (r : NRec)
    (hr : B.ns !! n = some r) (hp0 : r.nv.pgid' ≠ W64 0) (pg : List w8)
    (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) :
    X.posExtent bl r.nv.pgid' = some (r.nv.pgid', 1 + pageOverflow pg) := by
  unfold WX.posExtent
  rw [hb]
  simp only [resolve_node B X.v _ bl hc h0 n r hr, hr, Option.map_some, Option.getD_some,
    if_neg hp0, hpg]

end pos

end bbolt
end EtcdGrove
end Perennial
