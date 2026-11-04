/-
At `Commit`: the writer's well-formedness (`wOK`) makes every bucket ready for `rebalance`
(`rblB … none`, `RblDefs.lean`): `rblB_of_wOK`. Ported from `old/bbolt/.../RebalanceReady.lean`
(pure part; the old `rblReady_of_shape` read the same facts out of `ownWriteTx`/`txShape`).

Everything but the exact keys comes from the nodes' pages (`txPg`) and the view's page heights
(`pageHts`, from `viewWF`'s `treeOK`):
- heights (`rblHt`): a leaf 0, a branch its page's height (`pht`), which is one more than its
  children's pages', hence than its materialized children (a leaf child was read from a leaf
  page, of height 0; a branch child has its page's height);
- the parent pointers have no cycle (`rblAcyc`): a node is an entry of its parent's (`nodeClean`),
  so the parent is one higher;
- a leaf's entries have `pgid` 0 (`leafPg0`);
- a branch's lower bound is its first key (`brFirst`): the lower bound is the parent's entry's
  key (the node's key, its first entry's) or, under the parent's first entry, the parent's lower
  bound, its first key by induction up the parent chain (on the heights: the nodes are finitely
  many, so their heights are bounded).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace RblReady

section pure
variable [GooseExts]

theorem le_sum_of_mem (f : Loc → Nat) (L : List Loc) (k : Loc) (h : k ∈ L) :
    f k ≤ (L.map f).sum := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- A function is bounded on a finite map's keys. -/
theorem bound (m : GMap Loc NRec) (f : Loc → Nat) : ∃ N, ∀ k, (m !! k).isSome → f k ≤ N := by
  obtain ⟨L, hL⟩ := m.finite
  exact ⟨(L.map f).sum, fun k hk => le_sum_of_mem f L k (hL k hk)⟩

/-- The heights of the nodes: a leaf 0, a branch its page's. -/
def ht (B : BRec) (pht : Nat → Nat) (l : Loc) : Nat :=
  match B.ns !! l with
  | some r => if r.nv.isLeaf' = true then 0 else pht r.nv.pgid'.toNat
  | none => 0

theorem ht_of (B : BRec) (pht : Nat → Nat) (l : Loc) (r : NRec) (h : B.ns !! l = some r) :
    ht B pht l = if r.nv.isLeaf' = true then 0 else pht r.nv.pgid'.toNat := by
  unfold ht; rw [h]

theorem branchPgid_toNat (pg : List w8) (i : Nat) :
    (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
  have := (branchElem pg i).pgid'.isLt
  simp only [W64, BitVec.toNat_ofInt, branchPgid]; omega

/-- The nodes' pages of one bucket (`txPg`'s, for that bucket). -/
def bktPg (v : View) (B : BRec) : Prop := ∀ l r, B.ns !! l = some r → nodePg v B.ib.root' r

section bkt
variable (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean v hwm bl B)
  (hp : bktPg v B) (pht : Nat → Nat) (hph : pageHts v.pages pht)
include hc hp hph

/-- A branch is one higher than its children, nodes or pages. -/
theorem ht_branch (l : Loc) (r : NRec) (hl : B.ns !! l = some r) (hb : r.nv.isLeaf' = false)
    (w : WEntry) (hw : w ∈ r.ws) :
    (∀ l', B.nm !! w.pgid = some l' → ht B pht l' + 1 = ht B pht l) ∧
    (B.nm !! w.pgid = none → pht w.pgid.toNat + 1 = ht B pht l) := by
  obtain ⟨-, -, -, -, hc5, -, hc7, -, -, -⟩ := hc
  obtain ⟨-, pg, hpg, hfl, hlen, hpid⟩ := (hp l r hl).2 hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
  have hlt : i < pageCount pg := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  have hwp := hpid i w hi
  have hu : w.pgid.toNat = branchPgid pg i := by
    rw [hwp]; exact branchPgid_toNat pg i
  have hh := (hph _ pg hpg).2 hfl i hlt
  have hl' : ht B pht l = pht r.nv.pgid'.toNat := by rw [ht_of B pht l r hl, hb]; rfl
  refine ⟨fun l' hl'' => ?_, fun _ => by rw [hl', hu]; exact hh⟩
  obtain ⟨-, r', hr', hpg'⟩ := hc5 _ _ hl''
  have hr0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc7 h0 l r hl; rw [hb] at this; cases this
  rw [hl', ht_of B pht l' r' hr', ← hh, ← hu]
  cases hlf : r'.nv.isLeaf'
  · rw [if_neg (by simp), hpg']
  · rw [if_pos rfl]
    obtain ⟨q, hq, hqf⟩ := ((hp l' r' hr').1 hlf).2 hr0
    rw [hpg'] at hq
    rw [(hph _ q hq).1 hqf]

/-- The heights (`rblHt`). -/
theorem rblHt_of : rblHt v B :=
  ⟨ht B pht, pht, hph, fun l r hl =>
    ⟨fun hlf => by rw [ht_of B pht l r hl, if_pos hlf],
     fun hb w hw => ht_branch v hwm bl B hc hp pht hph l r hl hb w hw⟩⟩

/-- A node's parent is one higher. -/
theorem ht_parent (l : Loc) (r : NRec) (hl : B.ns !! l = some r) (hpn : r.nv.parent' ≠ null) :
    ∃ rp, B.ns !! r.nv.parent' = some rp ∧ rp.nv.isLeaf' = false ∧
      ht B pht l + 1 = ht B pht r.nv.parent' := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, h15, -⟩ := hc.2.2.2.2.2.2.2.1 l r hl
  obtain ⟨rp, hrp, hb, -, w, hw, hwp⟩ := h15 hpn
  refine ⟨rp, hrp, hb, ?_⟩
  exact (ht_branch v hwm bl B hc hp pht hph _ rp hrp hb w hw).1 l (by rw [hwp]; exact h8)

/-- No cycle of parent pointers (`rblAcyc`). -/
theorem rblAcyc_of : rblAcyc B :=
  ⟨ht B pht, fun l r hl hpn => by
    obtain ⟨-, -, -, h⟩ := ht_parent v hwm bl B hc hp pht hph l r hl hpn; omega⟩

/-- A branch's lower bound is its first key (`brFirst`). -/
theorem brFirst_of (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB v B bnd) :
    brFirst B bnd := by
  obtain ⟨N, hN⟩ := bound B.ns (ht B pht)
  have key : ∀ d l r, B.ns !! l = some r → N - ht B pht l ≤ d → r.nv.isLeaf' = false →
      ∀ x, (bnd l).1 = some x → wKey r.ws 0 = x := by
    intro d
    induction d with
    | zero =>
      intro l r hl hd hb x hx
      obtain ⟨-, c2, -⟩ := hk.2.2 l r hl
      by_cases hpn : r.nv.parent' = null
      · rw [c2 hpn] at hx; cases hx
      · obtain ⟨rp, hrp, -, h⟩ := ht_parent v hwm bl B hc hp pht hph l r hl hpn
        have := hN _ (by rw [hrp]; rfl); omega
    | succ d ih =>
      intro l r hl hd hb x hx
      obtain ⟨-, c2, c3, -⟩ := hk.2.2 l r hl
      by_cases hpn : r.nv.parent' = null
      · rw [c2 hpn] at hx; cases hx
      obtain ⟨-, rp, i, w, hrp, hw, -, hwk, hbe⟩ := c3 hpn
      have hrk : r.key = wKey r.ws 0 := ((hp l r hl).2 hb).1
      have hwi : (rp.ws.map WEntry.key).getD i [] = w.key := by
        simp [List.getD_eq_getElem?_getD, hw]
      rw [hbe] at hx
      unfold wEntryBnd entryBnd childLo at hx
      simp only at hx
      split at hx
      · rename_i hi0
        subst hi0
        obtain ⟨rp', hrp', hbp, h⟩ := ht_parent v hwm bl B hc hp pht hph l r hl hpn
        rw [hrp] at hrp'; cases hrp'
        have hNp := hN _ (by rw [hrp]; rfl)
        have := ih _ rp hrp (by omega) hbp x hx
        have hw0 : wKey rp.ws 0 = w.key := by simp [wKey, hw]
        rw [← hrk, ← hwk, ← hw0, this]
      · cases hx
        rw [← hrk, ← hwk, ← hwi]
  intro l r hl hb x hx
  exact key _ l r hl (Nat.le_refl _) hb x hx

end bkt

/-- The leaves' entries have no child page (`leafPg0`). -/
theorem leafPg0_of (v : View) (B : BRec) (hp : bktPg v B) : leafPg0 B :=
  fun l r hl hlf => ((hp l r hl).1 hlf).1

end pure

end RblReady

section pure
variable [GooseExts]

/-- A well-formed view's pages have heights (`treeOK`'s `treeStrict`). -/
theorem pageHts_of_viewWF (v : View) (h : viewWF v) : ∃ pht, pageHts v.pages pht := by
  obtain ⟨C, hC, hv⟩ := h
  rw [← hv]
  exact hC.1.2.2.2

/-- At `Commit`: the clean transaction's buckets with their keys and their nodes' pages, over a
view whose pages have heights, are ready for `rebalance`. -/
theorem rblReady_of (X : WX) (hc : txClean X) (hpht : ∃ pht, pageHts X.v.pages pht)
    (hk : ∀ bl B, X.t.bs !! bl = some B → bktKeys X.v B) (hp : txPg X.v X.t.bs) :
    rblReady X.v X.t := by
  obtain ⟨pht, hph⟩ := hpht
  intro bl B hB
  have hcl := (hc.2.2.2.2.2 bl B hB).1
  have hpB : RblReady.bktPg X.v B := hp bl B hB
  obtain ⟨bnd, hkb⟩ := hk bl B hB
  exact ⟨⟨bnd, hkb, RblReady.brFirst_of X.v _ bl B hcl hpB pht hph bnd hkb⟩,
    RblReady.leafPg0_of X.v B hpB, RblReady.rblAcyc_of X.v _ bl B hcl hpB pht hph,
    RblReady.rblHt_of X.v _ bl B hcl hpB pht hph⟩

/-- At `Commit`, `wOK` gives every bucket in the rebalance invariant with no deficient node
(the new form of the old `rblReady_of_shape`). -/
theorem rblB_of_wOK (X : WX) (h : wOK X) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B) :
    rblB X.v X.t.mv.pgid'.toNat bl B none := by
  obtain ⟨hc, hk, hp, -, -, -, -, hv⟩ := h
  obtain ⟨⟨bnd, hkb, hbf⟩, hl0, ha, hh⟩ :=
    rblReady_of X hc (pageHts_of_viewWF X.v hv) (fun bl B hB => (hk bl B hB).1) hp bl B hB
  exact ⟨(hc.2.2.2.2.2 bl B hB).1, ⟨bnd, rblKeysB_of X.v B bnd hkb hbf hl0⟩, ha, hh⟩

/-- `wOK` gives `brFirst` of each bucket (for some exact bounds) and the leaves' `pgid` 0. -/
theorem rblReady_of_wOK (X : WX) (h : wOK X) : rblReady X.v X.t := by
  obtain ⟨hc, hk, hp, -, -, -, -, hv⟩ := h
  exact rblReady_of X hc (pageHts_of_viewWF X.v hv) (fun bl B hB => (hk bl B hB).1) hp

end pure

end bbolt
end EtcdGrove
end Perennial
