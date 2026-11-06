/-
`Bucket.spill` (U9o, `notes/bbolt-proof-plan.md`): **a nested bucket's entries are plain**, the
part of `bkPre` (`Spill/BktSpec`) about its elements: the leaf entries of its logical tree (its
nodes' and, at its page positions, its view pages') carry no bucket flag, a non-empty key, and fit
`bboltEntryMax` (`plainEls`); so its elements, as key/value pairs, are its plain entries
(`lbktEnts`).

The premises are stated over the bucket's record: its leaf nodes' entries plain (`leafShape` and
`entriesBounded` for a bucket other than the root), and its view leaf pages under its page
positions plain (`posShape` for a bucket other than the root, batch 38's S1).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSpec
public import Proof.go_etcd_io.bbolt.Spill.BktInit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section plain
variable [GooseExts]

/-- A flag is not a bucket's iff its low bit is clear. -/
theorem notBkt_iff (f : w32) : ¬ isBktFlag f ↔ f.toNat % 2 = 0 := by
  unfold isBktFlag
  have hk : (f &&& W32 1).toNat = f.toNat % 2 := by
    rw [BitVec.toNat_and]; show f.toNat &&& 1 = f.toNat % 2; rw [Nat.and_one_is_mod]
  rw [Classical.not_not]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [hk] at this; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; rw [hk, h]; rfl

/-- **A plain leaf entry** (by its element: `plainEls`'s clause). -/
def plainE (w : WEntry) : Prop :=
  w.flags.toNat % 2 = 0 ∧ 0 < w.key.length ∧ w.key.length + w.value.length ≤ bboltEntryMax

/-- The leaves `leavesF` reaches in a well-formed tree are well-formed leaf pages below it. -/
theorem leavesF_wf (P : Pages) (hwm : Nat) :
    ∀ (n id : Nat), treeWF P hwm id → ∀ pg ∈ leavesF n P id,
      ∃ p, ownHas P id p ∧ P !! p = some pg ∧ pageFlags pg = leafPageFlag ∧ leafWF pg pg.length
  | 0, _, _, pg, h => by simp [leavesF] at h
  | n + 1, id, hw, pg', h => by
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
      by_cases hfl : pageFlags pg = leafPageFlag
      · simp only [leavesF, hpg, hfl, if_true, List.mem_singleton] at h
        subst h
        cases hpt with
        | leaf _ _ _ hwf _ => exact ⟨id, ownHas.root id pg' hpg, hpg, hfl, hwf⟩
        | branch _ _ hb _ _ => rw [hfl] at hb; cases hb
      · simp only [leavesF, hpg, hfl, if_false, List.mem_flatMap, List.mem_range] at h
        obtain ⟨j, hj, hm⟩ := h
        cases hpt with
        | leaf _ _ hf _ _ => exact absurd hf hfl
        | branch _ _ hfb _ hch =>
          obtain ⟨p, ho, h2⟩ := leavesF_wf P hwm n _ (hch j hj) pg' hm
          exact ⟨p, ownHas.child id pg j p hpg hfb hj ho, h2⟩

/-- A well-formed leaf page's entry `j` reads its key and value in full. -/
theorem leafKey_len {pg : List w8} (hwf : leafWF pg pg.length) {j : Nat} (hj : j < pageCount pg) :
    (leafKey pg j).length = leafKsize pg j ∧ (leafValue pg j).length = leafVsize pg j := by
  have hb := (hwf.2.2.1 j hj).1
  constructor
  · unfold leafKey bytesAt; simp only [List.length_take, List.length_drop]; omega
  · unfold leafValue bytesAt; simp only [List.length_take, List.length_drop]; omega

/-- The logical tree over a page position's subtree of a clean bucket reads its view pages. -/
theorem ltree_pages_clean {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C)
    (hcl : bktClean X.v X.t.mv.pgid'.toNat c C) {l : Loc} {r : NRec} {i : Nat} {w : WEntry}
    (hr : C.ns !! l = some r) (hl : r.nv.isLeaf' = false) (hw : r.ws[i]? = some w)
    (hnm : C.nm !! w.pgid = none) :
    ∀ q : w64, treeHas X.v.pages w.pgid.toNat q.toNat →
      ltree X c q = (X.v.pages !! q.toNat).map pgRead := by
  intro q hq
  have h0 : C.ib.root' ≠ W64 0 := by
    intro e; have := hcl.2.2.2.2.2.2.1 e l r hr; rw [hl] at this; cases this
  have hpos : pagePosAt C l i w.pgid := ⟨r, w, hr, hl, hw, rfl, hnm⟩
  have hfree := hcl.2.2.2.2.2.2.2.2.2.1 l i w.pgid hpos q.toNat hq
  rw [show W64 (q.toNat : Int) = q by simp] at hfree
  unfold ltree; rw [hC]; simp only
  have hres : resolve C q = none := by unfold resolve; rw [if_neg h0]; exact hfree
  rw [hres]; simp only
  unfold wpageAt; rw [if_neg h0, Option.map_map]; rfl

/-- **The leaves of a clean bucket's logical tree, from a node, are plain**, when its leaf nodes'
entries are and its view leaf pages under its page positions are. -/
theorem lleaves_plain {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C)
    (hcl : bktClean X.v X.t.mv.pgid'.toNat c C)
    (hnode : ∀ l r, C.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, plainE w)
    (hpage : ∀ c0 p pg, posRoot C c0 → ownHas X.v.pages c0 p → X.v.pages !! p = some pg →
      pageFlags pg = leafPageFlag → ∀ i < pageCount pg,
        leafFlags pg i % 2 = 0 ∧ 0 < leafKsize pg i ∧ leafKsize pg i + leafVsize pg i ≤ bboltEntryMax) :
    ∀ n pid l r, resolve C pid = some l → C.ns !! l = some r →
      ∀ ws ∈ lleaves (ltree X) c n pid, ∀ w ∈ ws, plainE w
  | 0, _, _, _, _, _, ws, hws => by simp [lleaves] at hws
  | n + 1, pid, l, r, hres, hr, ws, hws => by
    have hL : ltree X c pid = some (r.nv.isLeaf', r.ws) := by
      unfold ltree; rw [hC]; simp only; rw [hres]; simp only [hr, Option.map_some]
    cases hleaf : r.nv.isLeaf' with
    | true =>
      simp only [lleaves, hL, hleaf, List.mem_singleton] at hws
      subst hws
      exact hnode l r hr hleaf
    | false =>
      simp only [lleaves, hL, hleaf, List.mem_flatMap] at hws
      obtain ⟨we, hwe, hws'⟩ := hws
      have h0 : C.ib.root' ≠ W64 0 := by
        intro e; have := hcl.2.2.2.2.2.2.1 e l r hr; rw [hleaf] at this; cases this
      cases hnm : C.nm !! we.pgid with
      | some l' =>
        obtain ⟨-, r', hr', -⟩ := hcl.2.2.2.2.1 _ _ hnm
        exact lleaves_plain hC hcl hnode hpage n we.pgid l' r' (resolve_nm h0 hnm) hr' ws hws'
      | none =>
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hwe
        have hnc := hcl.2.2.2.2.2.2.2.1 l r hr
        have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat we.pgid.toNat :=
          ((hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf).2.2 we hwe).2.2 hnm
        rw [lleaves_pages (ltree X) c X.v.pages X.t.mv.pgid'.toNat n we.pgid hwf
          (ltree_pages_clean hC hcl hr hleaf hi hnm)] at hws'
        obtain ⟨pg, hpg, rfl⟩ := List.mem_map.1 hws'
        obtain ⟨p, hown, hp, hfl, hlwf⟩ := leavesF_wf _ _ n _ hwf pg hpg
        have hpp : pagePosAt C l i (W64 (we.pgid.toNat : Int)) := by
          rw [show W64 (we.pgid.toNat : Int) = we.pgid by simp]
          exact ⟨r, we, hr, hleaf, hi, rfl, hnm⟩
        have hpos : posRoot C we.pgid.toNat := Or.inr ⟨l, i, hpp, we.pgid.isLt⟩
        intro w hw
        unfold pageWs at hw
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
        have hj' := List.mem_range.1 hj
        obtain ⟨e1, e2, e3⟩ := hpage _ p pg hpos hown hp hfl j hj'
        obtain ⟨k1, k2⟩ := leafKey_len hlwf hj'
        have hfx : (W32 (leafFlags pg j : Int)).toNat = leafFlags pg j := by
          have := leafFlags_lt pg j
          rw [BitVec.toNat_ofInt]; simp; omega
        simp only [plainE, pageW, if_pos hfl]
        rw [hfx, k1, k2]
        exact ⟨e1, e2, e3⟩

/-- **A nested bucket's elements are plain, and are its plain entries** (`bkPre`'s last two
clauses): the elements `E` of its leaves from its root, as `uTree_init_node` gives them. -/
theorem bk_plain {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C)
    (hcl : bktClean X.v X.t.mv.pgid'.toNat c C) (hrn : C.bv.rootNode' ≠ null)
    (hnode : ∀ l r, C.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, plainE w)
    (hpage : ∀ c0 p pg, posRoot C c0 → ownHas X.v.pages c0 p → X.v.pages !! p = some pg →
      pageFlags pg = leafPageFlag → ∀ i < pageCount pg,
        leafFlags pg i % 2 = 0 ∧ 0 < leafKsize pg i ∧ leafKsize pg i + leafVsize pg i ≤ bboltEntryMax)
    {E : List El} (hE : (lleaves (ltree X) c X.fuel C.ib.root').flatMap (List.map wEl) = E) :
    plainEls E ∧ E.map (fun e => (e.2.1, e.2.2)) = lbktEnts X c := by
  obtain ⟨r0, hr0⟩ : ∃ r0, C.ns !! C.bv.rootNode' = some r0 := by
    obtain ⟨r, hr, -⟩ := (hcl.2.2.2.2.1 _ _ (hcl.2.2.2.1 hrn)).2; exact ⟨r, hr⟩
  have hres : resolve C C.ib.root' = some C.bv.rootNode' := by
    unfold resolve
    by_cases h0 : C.ib.root' = W64 0
    · rw [if_pos h0, if_neg hrn]
    · rw [if_neg h0]; exact hcl.2.2.2.1 hrn
  have hall := lleaves_plain hC hcl hnode hpage X.fuel C.ib.root' _ r0 hres hr0
  subst hE
  constructor
  · intro e he
    obtain ⟨ws, hws, he'⟩ := List.mem_flatMap.1 he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he'
    exact hall ws hws w hw
  · have hrp : X.rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hC]; rfl
    unfold lbktEnts WX.leaves; rw [hrp, List.map_flatMap]
    apply flatMap_congr_els
    intro ws hws
    rw [List.map_map]
    have : ∀ w ∈ ws, ¬ isBktFlag w.flags := fun w hw => (notBkt_iff _).2 (hall ws hws w hw).1
    clear hall hws
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      rw [List.map_cons, List.filterMap_cons,
        if_neg (by simpa using this w (List.mem_cons_self ..)),
        ih (fun w' hw' => this w' (List.mem_cons_of_mem _ hw'))]
      rfl

end plain

end Spill

end bbolt
end EtcdGrove
end Perennial
