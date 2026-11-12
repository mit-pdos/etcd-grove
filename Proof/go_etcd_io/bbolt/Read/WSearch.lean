/-
The writer's search (U6d, `notes/bbolt-proof-plan.md`), pure facts for `Cursor.search_w`'s
proof: `searchNode`'s index routes the key (`sn_route`, the node version of the reader's
`sp_route`), and the facts of a searchable page position (`posOK_page_facts`: what
`Bucket.pageNode_w` takes, and the page's leaf or branch well-formedness).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WPos
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wsearch
variable [GooseExts]

/-- `searchNode`'s exact-match flag: some evaluated key is `kb`. -/
def snExact (ws : List WEntry) (kb : List w8) (L : List Int) : Bool :=
  decide (∃ j ∈ L, wKey ws j.toNat = kb)

/-- Index `i` of the entries `ws` routes `k`: the last entry whose key is at most `k`, or the
first. -/
def nRoute (ws : List WEntry) (k : List w8) (i : Nat) : Prop :=
  i < ws.length ∧ (i = 0 ∨ ¬ go.GoStringLt k (wKey ws i)) ∧
    (i + 1 < ws.length → go.GoStringLt k (wKey ws (i + 1)))

omit [GooseExts] in
/-- **`searchNode`'s index routes the key** (as the reader's `sp_route`). -/
theorem sn_route (ws : List WEntry) (kb : List w8) (L : List Int) (idx : Int)
    (hc0 : 0 < ws.length) (hsorted : wsSorted ws) (H0 : 0 ≤ idx)
    (Hfound : idx < ws.length → Write.gePred ws kb idx = true)
    (Hoob : (∀ i : Int, 0 ≤ i ∧ i < (ws.length : Int) → Write.gePred ws kb i = false) →
      idx = ws.length)
    (Hgt : ∀ k : Int, 0 ≤ k ∧ k < idx → Write.gePred ws kb k = false)
    (Hev : idx < ws.length → idx ∈ L) (hL : ∀ j ∈ L, 0 ≤ j ∧ j < (ws.length : Int)) :
    let ri := if snExact ws kb L = true then idx else if 0 < idx then idx - 1 else idx
    nRoute ws kb ri.toNat ∧ 0 ≤ ri ∧ ri < ws.length := by
  intro ri
  have hle : idx ≤ ws.length := by
    rcases Int.lt_or_le (ws.length : Int) idx with hc | hc
    · have := Hoob (fun k hk => Hgt k ⟨hk.1, by omega⟩); omega
    · exact hc
  simp only [Write.gePred, decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not] at Hfound Hgt
  by_cases hex : snExact ws kb L = true
  · simp only [ri, hex, ↓reduceIte]
    simp only [snExact, decide_eq_true_eq] at hex
    obtain ⟨j, hj, hjk⟩ := hex
    obtain ⟨hj0, hjn⟩ := hL j hj
    have hji : ¬ j < idx := fun h => go.goStringLt_irrefl kb (hjk ▸ Hgt j ⟨hj0, h⟩)
    have hidx : idx < ws.length := by omega
    have hfi := Hfound hidx
    have hjeq : j = idx := by
      rcases Int.lt_or_le idx j with h | h
      · exfalso; apply hfi; rw [← hjk]
        exact hsorted idx.toNat j.toNat (by omega) (by omega)
      · omega
    subst hjeq
    refine ⟨⟨by omega, Or.inr (by rw [hjk]; exact go.goStringLt_irrefl _), fun h1 => ?_⟩, H0, hidx⟩
    rw [← hjk]; exact hsorted j.toNat (j.toNat + 1) (by omega) h1
  · simp only [ri, hex, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : idx < ws.length
    · have hin := Hev hlt
      have hne : wKey ws idx.toNat ≠ kb := by
        intro h; apply hex; simp only [snExact, decide_eq_true_eq]; exact ⟨idx, hin, h⟩
      have hgt : go.GoStringLt kb (wKey ws idx.toNat) := by
        rcases Classical.em (go.GoStringLt kb (wKey ws idx.toNat)) with h | h
        · exact h
        · exact absurd (go.goStringLt_eq_of_not_lt (Hfound hlt) h) hne
      by_cases h0 : 0 < idx
      · rw [if_pos h0]
        have hb := Hgt (idx - 1) ⟨by omega, by omega⟩
        refine ⟨⟨by omega, Or.inr (go.goStringLt_asymm hb), fun h1 => ?_⟩, by omega, by omega⟩
        rw [show (idx - 1).toNat + 1 = idx.toNat by omega]; exact hgt
      · rw [if_neg h0]
        have hi0 : idx = 0 := by omega
        refine ⟨⟨by omega, Or.inl (by omega), fun h1 => ?_⟩, H0, hlt⟩
        subst hi0
        exact go.goStringLt_trans hgt (hsorted 0 1 (by omega) (by simpa using h1))
    · have hin : idx = ws.length := by omega
      rw [if_pos (by omega)]
      have hb := Hgt (idx - 1) ⟨by omega, by omega⟩
      refine ⟨⟨by omega, Or.inr (go.goStringLt_asymm hb), fun h1 => by omega⟩, by omega, by omega⟩

omit [GooseExts] in
/-- `nRoute` is `lRoutes`' branch clause. -/
theorem nRoute_lroute (ws : List WEntry) (k : List w8) (i : Nat) (h : nRoute ws k i) :
    i < ws.length ∧ (i = 0 ∨ ∃ w, ws[i]? = some w ∧ ¬ go.GoStringLt k w.key) ∧
      ∀ w, ws[i + 1]? = some w → go.GoStringLt k w.key := by
  obtain ⟨hi, h0, h1⟩ := h
  refine ⟨hi, ?_, ?_⟩
  · rcases h0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨ws[i], by simp [hi], ?_⟩
      unfold wKey at h0; rw [List.getElem?_eq_getElem hi] at h0; exact h0
  · intro w hw
    have hlt : i + 1 < ws.length := by
      rcases Nat.lt_or_ge (i + 1) ws.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hw; cases hw
    have := h1 hlt
    unfold wKey at this; rw [hw] at this; exact this

/-- **The facts of a searchable page position** (no materialized node there): the page
`Bucket.pageNode_w` returns and its premises, and the page a leaf, or a branch of the view's tree
whose children are searchable. -/
theorem posOK_page_facts (X : WX) (bl : Loc) (B : BRec) (pid : w64)
    (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl) (hpm : pmFresh X) (hinl : inlSrcOK X bl)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF)
    (h : (resolve B pid = none ∧ B.ib.root' = W64 0 ∧ pid = W64 0) ∨
      (B.ib.root' ≠ W64 0 ∧ treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat ∧
        ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none)) :
    resolve B pid = none ∧ ∃ pa pg, wpageAt X.v B pid = some (pa, pg) ∧ 16 ≤ pg.length ∧
      (B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) ∧
      (B.ib.root' = W64 0 → B.bv.page' ≠ null) ∧
      (B.ib.root' ≠ W64 0 → X.t.pm !! pid = none ∧ 16 ≤ pg.length ∧ pageId pg = pid.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        pid.toNat * 4096 < 0xFFFFFFFFFFFF) ∧
      ((pageFlags pg = leafPageFlag ∧ leafWF pg pg.length) ∨
       (pageFlags pg = branchPageFlag ∧ B.ib.root' ≠ W64 0 ∧ X.v.pages !! pid.toNat = some pg ∧
        branchWF pg pg.length X.t.mv.pgid'.toNat ∧
        treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat ∧
        ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none)) := by
  obtain ⟨-, B', hB', hc, -⟩ := hloc
  rw [hB] at hB'; cases hB'
  rcases h with ⟨hres, h0, hp0⟩ | ⟨h0, ht, hnm⟩
  · have hrn : B.bv.rootNode' = null := by
      unfold resolve at hres; rw [if_pos h0] at hres
      by_cases hne : B.bv.rootNode' = null
      · exact hne
      · rw [if_neg hne] at hres; cases hres
    obtain ⟨hpg, -, hgood, -⟩ := hc.1 h0 hrn
    obtain ⟨-, hfl, hwf, h16, -⟩ := hgood
    refine ⟨hres, B.bv.page', B.ipg, ?_, h16, fun _ => ?_, fun _ => hpg, fun h => absurd h0 h,
      Or.inl ⟨hfl, hwf⟩⟩
    · unfold wpageAt; rw [if_pos h0, if_pos hp0]
    · rcases hinl B hB h0 hrn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, h⟩
  · obtain ⟨hres, pg, hpg, hw, hpt, hid, hlen⟩ := posOK_tree_page X B pid h0 ht hnm
    have h16 : 16 ≤ pg.length := by rw [hlen]; omega
    have hpmn : X.t.pm !! pid = none := by
      cases hp : X.t.pm !! pid with
      | none => rfl
      | some _ =>
        have := hpm pid (by rw [hp]; rfl)
        rw [hpg] at this; cases this
    refine ⟨hres, _, pg, hw, h16, fun h => absurd h h0, fun h => absurd h h0, fun _ => ?_, ?_⟩
    · refine ⟨hpmn, h16, hid, ?_, hmax _ pg hpg⟩
      cases hpt with
      | leaf _ _ hf _ _ => exact Or.inr hf
      | branch _ _ hf _ _ => exact Or.inl hf
    · cases hpt with
      | leaf _ _ hf hl _ => exact Or.inl ⟨hf, hl⟩
      | branch _ _ hf hb _ => exact Or.inr ⟨hf, h0, hpg, hb, ht, hnm⟩

end wsearch

end bbolt
end EtcdGrove
end Perennial
