/-
U7k (`notes/bbolt-proof-plan.md`): the bounds walk of a well-formed writer's bucket. Every block
of the walk from the root holds keys within the bounds the walk gives it, and these bounds are
pairwise disjoint: a key is in at most one block's bounds. The walk keeps `bInv`: at a
materialized node, its bounds are the node's `bnd` (`bktKeysB`); at a page, the page's subtree
has its keys within them (`treeKeys`) and no materialized page.
-/
module

public import Proof.go_etcd_io.bbolt.Write.DataWalk
public import Proof.go_etcd_io.bbolt.Write.WOk
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section databnd
variable [GooseExts]

/-! ## Bounds -/

theorem gs_lt_of_le_lt {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  by_cases h : a = b
  · subst h; exact h2
  · have : go.GoStringLt a b :=
      Classical.byContradiction fun hc => h (go.goStringLt_eq_of_not_lt hc h1)
    exact go.goStringLt_trans this h2

theorem keyIn_none (k : List w8) : keyIn none none k := by
  show keyGe none k ∧ keyLt k none
  refine ⟨?_, ?_⟩ <;> intro _ h <;> cases h

theorem wEntryBnd_eq (b : Bnd) (ws : List WEntry) (i : Nat) :
    wEntryBnd b ws i = (childLo b.1 (fun j => (ws.getD j default).key) i,
      childHi b.2 (fun j => (ws.getD j default).key) ws.length i) := by
  unfold wEntryBnd entryBnd childLo childHi
  simp only [List.length_map]
  congr 1
  · split
    · rfl
    · rename_i h
      congr 1
      by_cases hi : i < ws.length
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ i)]; rfl
  · split
    · rename_i h
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    · rfl

theorem wsPw_get (ws : List WEntry) (h : wsPw ws) (i j : Nat) (hij : i < j) (hj : j < ws.length) :
    go.GoStringLt (ws.getD i default).key (ws.getD j default).key := by
  unfold wsPw at h
  rw [List.pairwise_iff_getElem] at h
  have := h i j (by omega) hj hij
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (by omega : i < ws.length)] using this

theorem getD_mem (ws : List WEntry) (i : Nat) (h : i < ws.length) : ws.getD i default ∈ ws := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- A child's bounds are within its parent's. -/
theorem wEntryBnd_sub (b : Bnd) (ws : List WEntry) (_hs : wsPw ws)
    (hin : ∀ w ∈ ws, keyIn b.1 b.2 w.key) (i : Nat) (hi : i < ws.length) (k : List w8)
    (hk : keyIn (wEntryBnd b ws i).1 (wEntryBnd b ws i).2 k) : keyIn b.1 b.2 k := by
  rw [wEntryBnd_eq] at hk
  obtain ⟨hlo, hhi⟩ := hk
  constructor
  · intro l hl
    unfold childLo at hlo
    split at hlo
    · exact hlo l hl
    · have h1 := hlo _ rfl
      have h2 := (hin _ (getD_mem ws i hi)).1 l hl
      intro hkl
      exact h2 (gs_lt_of_le_lt h1 hkl)
  · intro h hh
    unfold childHi at hhi
    split at hhi
    · rename_i hi1
      have h1 := hhi _ rfl
      have h2 := (hin _ (getD_mem ws (i + 1) hi1)).2 h hh
      exact go.goStringLt_trans h1 h2
    · exact hhi h hh

/-- Siblings' bounds are disjoint. -/
theorem wEntryBnd_disj (b : Bnd) (ws : List WEntry) (hs : wsPw ws) (i j : Nat) (hij : i < j)
    (hj : j < ws.length) (k : List w8)
    (hk : keyIn (wEntryBnd b ws i).1 (wEntryBnd b ws i).2 k) :
    ¬ keyIn (wEntryBnd b ws j).1 (wEntryBnd b ws j).2 k := by
  rw [wEntryBnd_eq] at hk ⊢
  intro hk'
  have hhi := hk.2
  have hlo := hk'.1
  unfold childHi at hhi
  unfold childLo at hlo
  rw [if_pos (by omega : i + 1 < ws.length)] at hhi
  rw [if_neg (by omega : j ≠ 0)] at hlo
  have h1 := hhi _ rfl
  have h2 := hlo _ rfl
  apply h2
  by_cases he : i + 1 = j
  · rw [← he]; exact h1
  · exact go.goStringLt_trans h1 (wsPw_get ws hs (i + 1) j (by omega) hj)

theorem pw_mem_ne {α : Type} (R : α → α → Prop) (hR : ∀ x y, R x y → R y x) :
    ∀ (l : List α), l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y
  | [], _, x, hx, _, _, _ => by cases hx
  | a :: l, h, x, hx, y, hy, hxy => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact absurd rfl hxy
      · exact h.1 y hy'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact hR _ _ (h.1 x hx')
      · exact pw_mem_ne R hR l h.2 x hx' y hy' hxy

/-! ## Pages -/

theorem treeKeys_some (P : Pages) (p : Nat) (lo hi : Option (List w8)) (h : treeKeys P p lo hi) :
    ∃ pg, P !! p = some pg := by
  cases h with
  | leaf _ pg _ _ hpg => exact ⟨pg, hpg⟩
  | branch _ pg _ _ _ hpg => exact ⟨pg, hpg⟩

theorem w64_toNat_eq (p : w64) : W64 (p.toNat : Int) = p := by simp

theorem branchPgid_toNat (pg : List w8) (i : Nat) :
    (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
  unfold branchPgid; simp

/-- A branch page of a well-formed view has its keys sorted. -/
theorem viewWF_branch_sorted (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) :
    ∀ i j, i < j → j < pageCount pg → go.GoStringLt (branchKey pg i) (branchKey pg j) := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf _ _ => rw [hb] at hf; simp [branchPageFlag, leafPageFlag] at hf
    | branch _ _ _ hbw _ => exact hbw.2.2.2.2

theorem pageWs_len (pg : List w8) : (pageWs pg).length = pageCount pg := by
  unfold pageWs; simp

theorem pageWs_getD (pg : List w8) (i : Nat) (hi : i < pageCount pg) :
    (pageWs pg).getD i default = pageW pg i := by
  unfold pageWs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem pageW_branch (pg : List w8) (i : Nat) (hb : pageFlags pg ≠ leafPageFlag) :
    (pageW pg i).key = branchKey pg i ∧ (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
  unfold pageW; simp [hb]

theorem pageW_leaf (pg : List w8) (i : Nat) (hb : pageFlags pg = leafPageFlag) :
    (pageW pg i).key = leafKey pg i := by
  unfold pageW; simp [hb]

theorem childLo_congr (lo : Option (List w8)) (f g : Nat → List w8) (i : Nat)
    (h : f i = g i) : childLo lo f i = childLo lo g i := by
  unfold childLo; rw [h]

theorem childHi_congr (hi : Option (List w8)) (f g : Nat → List w8) (n i : Nat)
    (h : i + 1 < n → f (i + 1) = g (i + 1)) : childHi hi f n i = childHi hi g n i := by
  unfold childHi; split
  · rename_i hh; rw [h hh]
  · rfl

/-! ## The walk's invariant -/

variable (X : WX) (bl : Loc) (B : BRec) (bnd : Loc → Bnd)

/-- The walk's invariant at position `p` with bounds `b`. -/
def bInv (p : w64) (b : Bnd) : Prop :=
  (∃ m rm, resolve B p = some m ∧ B.ns !! m = some rm ∧ bnd m = b) ∨
  (B.ib.root' ≠ W64 0 ∧ treeKeys X.v.pages p.toNat b.1 b.2 ∧
    ∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) ∨
  (b = (none, none) ∧ ∀ ws, ltree X bl p ≠ some (false, ws))

variable (hok : wOK X) (hB : X.t.bs !! bl = some B) (hbk : bktKeysB X.v B bnd)
include hok hB hbk

theorem ltree_of_B (p : w64) : ltree X bl p = match resolve B p with
    | some l => (B.ns !! l).map fun r => (r.nv.isLeaf', r.ws)
    | none => (wpageAt X.v B p).map fun lp =>
        (decide (pageFlags lp.2 = leafPageFlag), pageWs lp.2) := by
  unfold ltree; rw [hB]; rfl

theorem bInv_page_ltree (p : w64) (hin : B.ib.root' ≠ W64 0)
    (hfree : ∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) (pg : List w8)
    (hpg : X.v.pages !! p.toNat = some pg) :
    ltree X bl p = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  rw [ltree_of_B X bl B bnd hok hB hbk]
  have hnm : B.nm !! p = none := by
    have := hfree p.toNat (treeHas.root _ pg hpg); rwa [w64_toNat_eq] at this
  have hr : resolve B p = none := by unfold resolve; rw [if_neg hin]; exact hnm
  rw [hr]
  unfold wpageAt; rw [if_neg hin, hpg]; rfl

theorem bInv_leaf (p : w64) (b : Bnd) (hI : bInv X bl B bnd p b) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) : ∀ w ∈ ws, keyIn b.1 b.2 w.key := by
  rcases hI with ⟨m, rm, hres, hrm, hbm⟩ | ⟨hin, htk, hfree⟩ | ⟨hb, -⟩
  · rw [ltree_of_B X bl B bnd hok hB hbk, hres] at hL
    simp only [hrm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    rw [← hbm]; exact (hbk.2.2 m rm hrm).1
  · obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk
    rw [bInv_page_ltree X bl B bnd hok hB hbk p hin hfree pg hpg] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hfl, rfl⟩ := hL
    intro w hw
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    rw [pageW_leaf pg i hfl]
    cases htk with
    | leaf _ pg' _ _ hpg' _ hkin _ => rw [hpg] at hpg'; cases hpg'; exact hkin i hi
    | branch _ pg' _ _ _ hpg' hbf =>
      rw [hpg] at hpg'; cases hpg'; rw [hfl] at hbf; simp [branchPageFlag, leafPageFlag] at hbf
  · subst hb; intro w _; exact keyIn_none _

theorem bInv_branch (p : w64) (b : Bnd) (hI : bInv X bl B bnd p b) (ws : List WEntry)
    (hL : ltree X bl p = some (false, ws)) :
    wsPw ws ∧ (∀ w ∈ ws, keyIn b.1 b.2 w.key) ∧
      ∀ i < ws.length, bInv X bl B bnd (ws.getD i default).pgid (wEntryBnd b ws i) := by
  have hc := wOK_bktClean X hok bl B hB
  rcases hI with ⟨m, rm, hres, hrm, hbm⟩ | ⟨hin, htk, hfree⟩ | ⟨-, hnb⟩
  · rw [ltree_of_B X bl B bnd hok hB hbk, hres] at hL
    simp only [hrm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hleaf, rfl⟩ := hL
    have hcl := hc.2.2.2.2.2.2.2.1 m rm hrm
    have hnk := hbk.2.2 m rm hrm
    have hin : B.ib.root' ≠ W64 0 := by
      intro h0; have := hc.2.2.2.2.2.2.1 h0 m rm hrm; rw [hleaf] at this; cases this
    have hnmp : B.nm !! p = some m := by unfold resolve at hres; rwa [if_neg hin] at hres
    have hmnull : m ≠ null := (hc.2.2.2.2.1 p m hnmp).1
    obtain ⟨-, hnd, hch⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
    refine ⟨wsSorted_pw _ hcl.2.2.2.1, by rw [← hbm]; exact hnk.1, ?_⟩
    intro i hi
    have hwi : rm.ws[i]? = some (rm.ws.getD i default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have hwm := getD_mem rm.ws i hi
    cases hnc : B.nm !! (rm.ws.getD i default).pgid with
    | some m' =>
      left
      obtain ⟨r', hr', hpar⟩ := (hch _ hwm).2.1 m' hnc
      obtain ⟨-, r'', hr'', hpg''⟩ := hc.2.2.2.2.1 _ m' hnc
      rw [hr'] at hr''; cases hr''
      have hnk' := hbk.2.2 m' r' hr'
      obtain ⟨-, rp, i', w', hrp, hw', hw'p, -, hbnd⟩ := hnk'.2.2.1 (by rw [hpar]; exact hmnull)
      rw [hpar, hrm] at hrp; cases hrp
      rw [hpar] at hbnd
      have hii : i' = i := by
        have hi' : i' < rm.ws.length := by
          rcases (List.getElem?_eq_some_iff.1 hw') with ⟨h, _⟩; exact h
        have e1 : (rm.ws.map WEntry.pgid)[i']'(by simpa using hi') =
            (rm.ws.map WEntry.pgid)[i]'(by simpa using hi) := by
          simp only [List.getElem_map]
          have := List.getElem?_eq_some_iff.1 hw'
          obtain ⟨_, h2⟩ := this
          rw [h2, hw'p, hpg'']
          have := List.getElem?_eq_some_iff.1 hwi
          obtain ⟨_, h3⟩ := this
          rw [h3]
        have hnd' := hnd
        unfold List.Nodup at hnd'
        rw [List.pairwise_iff_getElem] at hnd'
        rcases Nat.lt_trichotomy i' i with h | h | h
        · exact absurd e1 (hnd' i' i (by simpa using hi') (by simpa using hi) h)
        · exact h
        · exact absurd e1.symm (hnd' i i' (by simpa using hi) (by simpa using hi') h)
      subst hii
      refine ⟨m', r', ?_, hr', hbm ▸ hbnd⟩
      unfold resolve; rw [if_neg hin]; exact hnc
    | none =>
      right; left
      obtain ⟨-, kind, hkd⟩ := (hnk.2.2.2.1 hleaf)
      obtain ⟨pg, -, -, -, -, htk⟩ := (hkd i _ hwi).2 hnc
      refine ⟨hin, by rw [← hbm]; exact htk, ?_⟩
      intro d hd
      exact hc.2.2.2.2.2.2.2.2.2.1 m i _ ⟨rm, _, hrm, hleaf, hwi, rfl, hnc⟩ d hd
  · obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk
    rw [bInv_page_ltree X bl B bnd hok hB hbk p hin hfree pg hpg] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
    obtain ⟨hfl, rfl⟩ := hL
    cases htk with
    | leaf _ pg' _ _ hpg' hlf => rw [hpg] at hpg'; cases hpg'; exact absurd hlf hfl
    | branch _ pg' _ _ kind hpg' hbf h2 hkin hcpg hch =>
      rw [hpg] at hpg'; cases hpg'
      have hsort := viewWF_branch_sorted X.v hok.2.2.2.2.2.2.2 p.toNat pg hpg hbf
      have hkey : ∀ j < pageCount pg, ((pageWs pg).getD j default).key = branchKey pg j := by
        intro j hj; rw [pageWs_getD pg j hj]; exact (pageW_branch pg j hfl).1
      refine ⟨?_, ?_, ?_⟩
      · unfold wsPw; rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have hi' : i < pageCount pg := by rw [← pageWs_len]; exact hi
        have hj' : j < pageCount pg := by rw [← pageWs_len]; exact hj
        have e1 := hkey i hi'; have e2 := hkey j hj'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at e2
        simp only [Option.getD_some] at e1 e2
        rw [e1, e2]; exact hsort i j hij hj'
      · intro w hw
        unfold pageWs at hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
        rw [List.mem_range] at hi
        rw [(pageW_branch pg i hfl).1]; exact hkin i hi
      · intro i hi
        rw [pageWs_len] at hi
        right; left
        rw [pageWs_getD pg i hi, (pageW_branch pg i hfl).2, branchPgid_toNat]
        refine ⟨hin, ?_, ?_⟩
        · have hb' : wEntryBnd b (pageWs pg) i = (childLo b.1 (branchKey pg) i,
              childHi b.2 (branchKey pg) (pageCount pg) i) := by
            rw [wEntryBnd_eq, pageWs_len]
            congr 1
            · exact childLo_congr _ _ _ _ (hkey i hi)
            · exact childHi_congr _ _ _ _ _ (fun h => hkey (i + 1) h)
          rw [hb']; exact hch i hi
        · intro d hd
          exact hfree d (treeHas.sub _ pg d hpg (pageHas.child pg i d hbf hi hd))
  · exact absurd hL (hnb ws)

theorem bInv_root : bInv X bl B bnd (X.rootPid bl) (none, none) := by
  have hc := wOK_bktClean X hok bl B hB
  have hrp : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  rw [hrp]
  by_cases hin : B.ib.root' = W64 0
  · right; right
    refine ⟨rfl, fun ws hL => ?_⟩
    rw [ltree_of_B X bl B bnd hok hB hbk] at hL
    have hres : resolve B B.ib.root' =
        if B.bv.rootNode' = null then none else some B.bv.rootNode' := by
      unfold resolve; rw [if_pos hin]
    rw [hres] at hL
    by_cases hrn : B.bv.rootNode' = null
    · rw [if_pos hrn] at hL
      simp only at hL
      cases hp : wpageAt X.v B B.ib.root' with
      | none => rw [hp] at hL; cases hL
      | some x =>
        obtain ⟨pa, pg⟩ := x
        rw [hp] at hL
        have := wOK_inlineLeaf X bl _ hok B pa pg hB hin hrn hp
        simp [this] at hL
    · rw [if_neg hrn] at hL
      simp only at hL
      cases hr : B.ns !! B.bv.rootNode' with
      | none => simp only [hr] at hL; cases hL
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
        have := hc.2.2.2.2.2.2.1 hin _ r hr
        rw [hL.1] at this; cases this
  · by_cases hrn : B.bv.rootNode' = null
    · right; left
      refine ⟨hin, hbk.1 hrn hin, ?_⟩
      intro d _
      rw [(hc.2.2.1 hrn).2]; rfl
    · left
      have hnm := hc.2.2.2.1 hrn
      obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ _ hnm
      refine ⟨B.bv.rootNode', r, ?_, hr, ?_⟩
      · unfold resolve; rw [if_neg hin]; exact hnm
      · exact (hbk.2.2 _ r hr).2.1 (hbk.2.1 r hr)

/-- **The bounds walk**: from a position satisfying `bInv`, every block's keys are within its
bounds, which are within the start's, and the blocks' bounds are pairwise disjoint. -/
theorem bInv_walk : ∀ n p b, bInv X bl B bnd p b →
    (∀ x ∈ lleavesB (ltree X) bl n p b, ∀ w ∈ x.2.2, keyIn x.2.1.1 x.2.1.2 w.key) ∧
    (∀ x ∈ lleavesB (ltree X) bl n p b, ∀ k, keyIn x.2.1.1 x.2.1.2 k → keyIn b.1 b.2 k) ∧
    (lleavesB (ltree X) bl n p b).Pairwise
      (fun x y => ∀ k, keyIn x.2.1.1 x.2.1.2 k → ¬ keyIn y.2.1.1 y.2.1.2 k)
  | 0, _, _, _ => by simp [lleavesB]
  | n + 1, p, b, hI => by
    simp only [lleavesB]
    cases hL : ltree X bl p with
    | none => simp
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true =>
        simp only [List.mem_singleton, forall_eq, List.pairwise_singleton, and_true]
        exact ⟨bInv_leaf X bl B bnd hok hB hbk p b hI ws hL, fun k hk => hk⟩
      | false =>
        simp only
        obtain ⟨hs, hin, hch⟩ := bInv_branch X bl B bnd hok hB hbk p b hI ws hL
        have ih := fun i (hi : i < ws.length) =>
          bInv_walk n (ws.getD i default).pgid (wEntryBnd b ws i) (hch i hi)
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
          rw [List.mem_range] at hi
          exact (ih i hi).1 x hx
        · intro x hx k hk
          obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
          rw [List.mem_range] at hi
          exact wEntryBnd_sub b ws hs hin i hi k ((ih i hi).2.1 x hx k hk)
        · rw [List.pairwise_flatMap]
          refine ⟨fun i hi => (ih i (List.mem_range.1 hi)).2.2, ?_⟩
          apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
          intro i j hi hj hij x hx y hy k hk hk'
          rw [List.mem_range] at hi hj
          have h1 := (ih i hi).2.1 x hx k hk
          have h2 := (ih j hj).2.1 y hy k hk'
          exact wEntryBnd_disj b ws hs i j hij hj k h1 h2

end databnd

end Write

end bbolt
end EtcdGrove
end Perennial
