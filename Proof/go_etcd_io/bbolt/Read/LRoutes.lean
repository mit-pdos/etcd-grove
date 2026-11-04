/-
U6 (`notes/bbolt-proof-plan.md`): the writer's search lemma `lRoutes_found` (`Model/WOps`), as
`lRoutes_found'`, on a searchable bucket (`bktLocalOK`, so only `txPgLeaf`: a branch node's entries
need not be its page's). The walk of U7k's `Write/DataBnd` (`bInv`) is redone over the bucket's own
clean and key facts (`bInvL`), in place of `wOK`; a stack (`lRoute`, from `lPath`/`lRoutes`) is a
path of the walk whose bounds hold the key; it ends within the fuel, since its positions are
distinct pages of the view (a materialized prefix, distinct by the nodes' parent chain, then page
positions, distinct by `viewUnique`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Write.DataWalk
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace LR

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write

section lroutes
variable [GooseExts]

/-! ## Helpers (U7k's, `Write/DataBnd`, copied: that module needs `Write/WOk`'s heavier imports) -/

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

/-- **A route of `k`** through the logical tree `L` of bucket `bl`: each branch's index is the
last entry whose key is at most `k` (or the first), and selects the next position; it ends at a
leaf. -/
def lRoute (L : LTree) (bl : Loc) (k : List w8) : List w64 → Prop
  | [] => False
  | [p] => ∃ ws, L bl p = some (true, ws)
  | p :: q :: rest => ∃ ws i, L bl p = some (false, ws) ∧ i < ws.length ∧
      (i = 0 ∨ ¬ go.GoStringLt k (ws.getD i default).key) ∧
      (i + 1 < ws.length → go.GoStringLt k (ws.getD (i + 1) default).key) ∧
      (ws.getD i default).pgid = q ∧ lRoute L bl k (q :: rest)

/-- The routed child's bounds hold the key. -/
theorem route_keyIn (b : Bnd) (ws : List WEntry) (k : List w8) (hk : keyIn b.1 b.2 k) (i : Nat)
    (h0 : i = 0 ∨ ¬ go.GoStringLt k (ws.getD i default).key)
    (h1 : i + 1 < ws.length → go.GoStringLt k (ws.getD (i + 1) default).key) :
    keyIn (wEntryBnd b ws i).1 (wEntryBnd b ws i).2 k := by
  rw [wEntryBnd_eq]
  constructor
  · intro l hl
    unfold childLo at hl
    split at hl
    · exact hk.1 l hl
    · rename_i hne
      cases hl
      rcases h0 with h | h
      · exact absurd h hne
      · exact h
  · intro h hh
    unfold childHi at hh
    split at hh
    · rename_i hlt
      cases hh
      exact h1 hlt
    · exact hk.2 h hh

/-- In sorted entries, an entry's key is found at its search index. -/
theorem wsFound_of_mem : ∀ (ws : List WEntry), wsPw ws → ∀ w ∈ ws, wsFound ws w.key
  | [], _, w, hw => by cases hw
  | a :: t, hs, w, hw => by
    rw [wsPw, List.pairwise_cons] at hs
    rcases List.mem_cons.1 hw with rfl | hw'
    · unfold wsFound wsIdx
      rw [List.takeWhile_cons_of_neg (by simpa using go.goStringLt_irrefl w.key)]
      rfl
    · have ih := wsFound_of_mem t hs.2 w hw'
      have hlt := hs.1 w hw'
      unfold wsFound wsIdx at ih ⊢
      rw [List.takeWhile_cons_of_pos (by simpa using hlt), List.length_cons]
      simpa using ih

/-- A leaf page's entries are sorted when its keys are. -/
theorem pageWs_pw (pg : List w8) (hfl : pageFlags pg = leafPageFlag)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)) :
    wsPw (pageWs pg) := by
  unfold wsPw; rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < pageCount pg := by rw [← pageWs_len]; exact hi
  have hj' : j < pageCount pg := by rw [← pageWs_len]; exact hj
  have e1 := pageWs_getD pg i hi'
  have e2 := pageWs_getD pg j hj'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at e2
  simp only [Option.getD_some] at e1 e2
  rw [e1, e2, pageW_leaf pg i hfl, pageW_leaf pg j hfl]
  exact hs i j hij hj'

/-- A leaf page of a well-formed view has its keys sorted. -/
theorem viewWF_leaf_sorted (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = leafPageFlag) :
    ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j) := by
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
    | leaf _ _ _ hlw _ => exact hlw.2.2.2
    | branch _ _ hf _ _ => rw [hb] at hf; simp [branchPageFlag, leafPageFlag] at hf

/-- A well-formed view has no shared page (`viewUnique`). -/
theorem viewWF_unique (v : View) (hv : viewWF v) : viewUnique v.pages := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hP : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hP]; exact hok.1.2.1.2

/-! ## The parent chain -/

/-- A node's parent (`null` for `null` and for a location that is not a node). -/
def par (B : BRec) (m : Loc) : Loc :=
  if m = null then null else ((B.ns !! m).map fun r => r.nv.parent').getD null

/-- A node's `d`-th ancestor. -/
def anc (B : BRec) : Nat → Loc → Loc
  | 0, m => m
  | d + 1, m => anc B d (par B m)

theorem anc_null (B : BRec) : ∀ d, anc B d null = null
  | 0 => rfl
  | d + 1 => by
    show anc B d (par B null) = null
    rw [show par B null = null by unfold par; rw [if_pos rfl]]
    exact anc_null B d

theorem anc_add (B : BRec) (a : Nat) : ∀ b m, anc B (a + b) m = anc B a (anc B b m)
  | 0, _ => rfl
  | b + 1, m => by
    show anc B (a + b) (par B m) = anc B a (anc B b (par B m))
    exact anc_add B a b (par B m)

/-! ## The walk's invariant over a bucket's own facts -/

variable (X : WX) (bl : Loc) (B : BRec) (bnd : Loc → Bnd) (hwm : Nat)

/-- `Write.bInv` with the inline bucket's case explicit. -/
def bInvL (p : w64) (b : Bnd) : Prop :=
  (∃ m rm, resolve B p = some m ∧ B.ns !! m = some rm ∧ bnd m = b) ∨
  (B.ib.root' ≠ W64 0 ∧ treeKeys X.v.pages p.toNat b.1 b.2 ∧
    ∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) ∨
  (b = (none, none) ∧ B.ib.root' = W64 0 ∧ B.bv.rootNode' = null)

/-- The positions before `p` on a path from the root (`H`, the nearest first): with `p`, distinct
pages of the view; a materialized `p` has the materialized `H` as its ancestors; a page `p`'s
subtree holds none of them. -/
def hInv (H : List w64) (p : w64) : Prop :=
  ((p :: H).map fun q => q.toNat).Nodup ∧ (∀ q ∈ p :: H, (X.v.pages !! q.toNat).isSome) ∧
  (∀ m, resolve B p = some m → anc B H.length m = B.bv.rootNode' ∧
    ∀ i q, H[i]? = some q → resolve B q = some (anc B (i + 1) m)) ∧
  (resolve B p = none → ∀ q ∈ H, ¬ treeHas X.v.pages p.toNat q.toNat)

variable (hB : X.t.bs !! bl = some B) (hc : bktClean X.v hwm bl B) (hbk : bktKeysB X.v B bnd)
  (hv : viewWF X.v)
include hB hc hbk hv

theorem ltreeB (p : w64) : ltree X bl p = match resolve B p with
    | some l => (B.ns !! l).map fun r => (r.nv.isLeaf', r.ws)
    | none => (wpageAt X.v B p).map fun lp =>
        (decide (pageFlags lp.2 = leafPageFlag), pageWs lp.2) := by
  unfold ltree; rw [hB]; rfl

theorem pageL_ltree (p : w64) (hin : B.ib.root' ≠ W64 0)
    (hfree : ∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) (pg : List w8)
    (hpg : X.v.pages !! p.toNat = some pg) :
    ltree X bl p = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  rw [ltreeB X bl B bnd hwm hB hc hbk hv]
  have hnm : B.nm !! p = none := by
    have := hfree p.toNat (treeHas.root _ pg hpg); rwa [w64_toNat_eq] at this
  have hr : resolve B p = none := by unfold resolve; rw [if_neg hin]; exact hnm
  rw [hr]
  unfold wpageAt; rw [if_neg hin, hpg]; rfl

/-- An inline bucket without a root node: its position `0` is its inline page. -/
theorem inl_ltree (p : w64) (hin : B.ib.root' = W64 0) (hrn : B.bv.rootNode' = null) :
    ltree X bl p = if p = W64 0 then some (true, pageWs B.ipg) else none := by
  rw [ltreeB X bl B bnd hwm hB hc hbk hv]
  have hr : resolve B p = none := by unfold resolve; rw [if_pos hin, if_pos hrn]
  rw [hr]
  have hg := (hc.1 hin hrn).2.2.1
  unfold wpageAt; rw [if_pos hin]
  by_cases hp : p = W64 0
  · rw [if_pos hp, if_pos hp]; simp [hg.2.1]
  · rw [if_neg hp, if_neg hp]; rfl

/-- An inline bucket has no branch. -/
theorem inl_noBranch (hin : B.ib.root' = W64 0) (p : w64) (ws : List WEntry) :
    ltree X bl p ≠ some (false, ws) := by
  intro hL
  by_cases hrn : B.bv.rootNode' = null
  · rw [inl_ltree X bl B bnd hwm hB hc hbk hv p hin hrn] at hL
    split at hL
    · simp at hL
    · cases hL
  · rw [ltreeB X bl B bnd hwm hB hc hbk hv] at hL
    have hr : resolve B p = some B.bv.rootNode' := by unfold resolve; rw [if_pos hin, if_neg hrn]
    rw [hr] at hL
    simp only at hL
    cases hrm : B.ns !! B.bv.rootNode' with
    | none => rw [hrm] at hL; cases hL
    | some rm =>
      rw [hrm] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      have := hc.2.2.2.2.2.2.1 hin _ rm hrm
      rw [hL.1] at this; cases this

theorem bInvL_leaf (p : w64) (b : Bnd) (hI : bInvL X B bnd p b) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) : wsPw ws ∧ ∀ w ∈ ws, keyIn b.1 b.2 w.key := by
  rcases hI with ⟨m, rm, hres, hrm, hbm⟩ | ⟨hin, htk, hfree⟩ | ⟨hb, hin, hrn⟩
  · rw [ltreeB X bl B bnd hwm hB hc hbk hv, hres] at hL
    simp only [hrm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    refine ⟨wsSorted_pw _ (hc.2.2.2.2.2.2.2.1 m rm hrm).2.2.2.1, ?_⟩
    rw [← hbm]; exact (hbk.2.2 m rm hrm).1
  · obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk
    rw [pageL_ltree X bl B bnd hwm hB hc hbk hv p hin hfree pg hpg] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hfl, rfl⟩ := hL
    refine ⟨pageWs_pw pg hfl (viewWF_leaf_sorted X.v hv _ pg hpg hfl), ?_⟩
    intro w hw
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    rw [pageW_leaf pg i hfl]
    cases htk with
    | leaf _ pg' _ _ hpg' _ hkin _ => rw [hpg] at hpg'; cases hpg'; exact hkin i hi
    | branch _ pg' _ _ _ hpg' hbf =>
      rw [hpg] at hpg'; cases hpg'; rw [hfl] at hbf; simp [branchPageFlag, leafPageFlag] at hbf
  · rw [inl_ltree X bl B bnd hwm hB hc hbk hv p hin hrn] at hL
    split at hL
    · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hL
      subst hL
      have hg := (hc.1 hin hrn).2.2.1
      refine ⟨pageWs_pw _ hg.2.1 hg.2.2.1.2.2.2, ?_⟩
      subst hb; intro w _; exact keyIn_none _
    · cases hL

theorem bInvL_branch (p : w64) (b : Bnd) (hI : bInvL X B bnd p b) (ws : List WEntry)
    (hL : ltree X bl p = some (false, ws)) :
    wsPw ws ∧ (∀ w ∈ ws, keyIn b.1 b.2 w.key) ∧
      ∀ i < ws.length, bInvL X B bnd (ws.getD i default).pgid (wEntryBnd b ws i) := by
  rcases hI with ⟨m, rm, hres, hrm, hbm⟩ | ⟨hin, htk, hfree⟩ | ⟨-, hin, -⟩
  · rw [ltreeB X bl B bnd hwm hB hc hbk hv, hres] at hL
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
      exact hc.2.2.2.2.2.2.2.2.2 m i _ ⟨rm, _, hrm, hleaf, hwi, rfl, hnc⟩ d hd
  · obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk
    rw [pageL_ltree X bl B bnd hwm hB hc hbk hv p hin hfree pg hpg] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
    obtain ⟨hfl, rfl⟩ := hL
    cases htk with
    | leaf _ pg' _ _ hpg' hlf => rw [hpg] at hpg'; cases hpg'; exact absurd hlf hfl
    | branch _ pg' _ _ kind hpg' hbf h2 hkin hcpg hch =>
      rw [hpg] at hpg'; cases hpg'
      have hsort := viewWF_branch_sorted X.v hv p.toNat pg hpg hbf
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
  · exact absurd hL (inl_noBranch X bl B bnd hwm hB hc hbk hv hin p ws)

theorem rootPid_eq : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl

theorem bInvL_root : bInvL X B bnd (X.rootPid bl) (none, none) := by
  rw [rootPid_eq X bl B bnd hwm hB hc hbk hv]
  by_cases hrn : B.bv.rootNode' = null
  · by_cases hin : B.ib.root' = W64 0
    · right; right; exact ⟨rfl, hin, hrn⟩
    · right; left
      refine ⟨hin, hbk.1 hrn hin, ?_⟩
      intro d _
      rw [(hc.2.2.1 hrn).2]; rfl
  · left
    have hnm := hc.2.2.2.1 hrn
    obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ _ hnm
    refine ⟨B.bv.rootNode', r, ?_, hr, ?_⟩
    · unfold resolve
      split
      · rfl
      · exact hnm
    · exact (hbk.2.2 _ r hr).2.1 (hbk.2.1 r hr)

/-- **The bounds walk** (`Write.bInv_walk` over `bInvL`). -/
theorem bInvL_walk : ∀ n p b, bInvL X B bnd p b →
    (∀ x ∈ lleavesB (ltree X) bl n p b, ∀ w ∈ x.2.2, keyIn x.2.1.1 x.2.1.2 w.key) ∧
    (lleavesB (ltree X) bl n p b).Pairwise
      (fun x y => ∀ k, keyIn x.2.1.1 x.2.1.2 k → ¬ keyIn y.2.1.1 y.2.1.2 k) ∧
    (∀ x ∈ lleavesB (ltree X) bl n p b, ∀ k, keyIn x.2.1.1 x.2.1.2 k → keyIn b.1 b.2 k)
  | 0, _, _, _ => by simp [lleavesB]
  | n + 1, p, b, hI => by
    simp only [lleavesB]
    cases hL : ltree X bl p with
    | none => simp
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true =>
        simp only [List.mem_singleton, forall_eq, List.pairwise_singleton, true_and]
        exact ⟨(bInvL_leaf X bl B bnd hwm hB hc hbk hv p b hI ws hL).2, fun k hk => hk⟩
      | false =>
        simp only
        obtain ⟨hs, hin, hch⟩ := bInvL_branch X bl B bnd hwm hB hc hbk hv p b hI ws hL
        have ih := fun i (hi : i < ws.length) =>
          bInvL_walk n (ws.getD i default).pgid (wEntryBnd b ws i) (hch i hi)
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
          rw [List.mem_range] at hi
          exact (ih i hi).1 x hx
        · rw [List.pairwise_flatMap]
          refine ⟨fun i hi => (ih i (List.mem_range.1 hi)).2.1, ?_⟩
          apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
          intro i j hi hj hij x hx y hy k hk hk'
          rw [List.mem_range] at hi hj
          have h1 := (ih i hi).2.2 x hx k hk
          have h2 := (ih j hj).2.2 y hy k hk'
          exact wEntryBnd_disj b ws hs i j hij hj k h1 h2
        · intro x hx k hk
          obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
          rw [List.mem_range] at hi
          exact wEntryBnd_sub b ws hs hin i hi k ((ih i hi).2.2 x hx k hk)

/-! ## Paths: distinct pages, so within the fuel -/

theorem res_nm (hin : B.ib.root' ≠ W64 0) (p : w64) : resolve B p = B.nm !! p := by
  unfold resolve; rw [if_neg hin]

theorem par_root : par B B.bv.rootNode' = null := by
  unfold par
  split
  · rfl
  · rcases h : B.ns !! B.bv.rootNode' with _ | r
    · rfl
    · simp only [Option.map_some, Option.getD_some]; exact hbk.2.1 r h

theorem bInvL_page (hin : B.ib.root' ≠ W64 0) (p : w64) (b : Bnd) (hI : bInvL X B bnd p b) :
    (X.v.pages !! p.toNat).isSome := by
  rcases hI with ⟨m, rm, hres, hrm, -⟩ | ⟨-, htk, -⟩ | ⟨-, h0, -⟩
  · have hnm : B.nm !! p = some m := by
      rw [← res_nm X bl B bnd hwm hB hc hbk hv hin]; exact hres
    obtain ⟨-, r, hr, hpid⟩ := hc.2.2.2.2.1 p m hnm
    have hw := (hc.2.2.2.2.2.2.2.1 m r hr).2.2.2.2.2.2.2.2.2.1 hin
    rw [hpid] at hw
    cases hw with
    | page _ pg _ _ hpg _ _ _ => rw [hpg]; rfl
  · obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk; rw [hpg]; rfl
  · exact absurd h0 hin

theorem hInv_root (hin : B.ib.root' ≠ W64 0) : hInv X B [] (X.rootPid bl) := by
  have hI := bInvL_root X bl B bnd hwm hB hc hbk hv
  rw [rootPid_eq X bl B bnd hwm hB hc hbk hv] at hI ⊢
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    rw [hq]; exact bInvL_page X bl B bnd hwm hB hc hbk hv hin _ _ hI
  · intro m hm
    rw [res_nm X bl B bnd hwm hB hc hbk hv hin] at hm
    refine ⟨?_, fun i q h => by simp at h⟩
    show m = B.bv.rootNode'
    by_cases hrn : B.bv.rootNode' = null
    · have h0 : B.nm !! B.ib.root' = none := by rw [(hc.2.2.1 hrn).2]; rfl
      rw [h0] at hm; cases hm
    · rw [hc.2.2.2.1 hrn] at hm; cases hm; rfl
  · intro _ q hq; simp at hq

theorem hInv_len (H : List w64) (p : w64) (h : hInv X B H p) : H.length + 1 ≤ X.v.pages.size := by
  obtain ⟨hnd, hpgs, -, -⟩ := h
  have hsub : (p :: H).map (fun q => q.toNat) ⊆ X.v.pages.toList.map Prod.fst := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 (hpgs q hq)
    exact List.mem_map.2 ⟨(q.toNat, pg), (GMap.mem_toList _ _ _).2 hpg, rfl⟩
  have := hnd.length_le_of_subset hsub
  unfold GMap.size
  simpa using this

theorem hInv_step (hin : B.ib.root' ≠ W64 0) (H : List w64) (p : w64) (b : Bnd)
    (hH : hInv X B H p) (hI : bInvL X B bnd p b) (ws : List WEntry)
    (hL : ltree X bl p = some (false, ws)) (i : Nat) (hi : i < ws.length) (c : w64)
    (hcd : (ws.getD i default).pgid = c) : hInv X B (p :: H) c := by
  have hcI : bInvL X B bnd c (wEntryBnd b ws i) :=
    hcd ▸ (bInvL_branch X bl B bnd hwm hB hc hbk hv p b hI ws hL).2.2 i hi
  have hcpg := bInvL_page X bl B bnd hwm hB hc hbk hv hin c _ hcI
  have hres := res_nm X bl B bnd hwm hB hc hbk hv hin
  obtain ⟨hnd, hpgs, hnode, hpage⟩ := hH
  have hpgs' : ∀ q ∈ c :: p :: H, (X.v.pages !! q.toNat).isSome := by
    intro q hq
    rcases List.mem_cons.1 hq with h | hq'
    · rw [h]; exact hcpg
    · exact hpgs q hq'
  have hnd_of : (∀ q ∈ p :: H, ¬ treeHas X.v.pages c.toNat q.toNat) →
      ((c :: p :: H).map fun q => q.toNat).Nodup := by
    intro hnot
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hmem
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hmem
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 hcpg
    exact hnot q hq (by rw [hqe]; exact treeHas.root _ pg hpg)
  cases hrp : resolve B p with
  | some m =>
    have hL' := hL
    rw [ltreeB X bl B bnd hwm hB hc hbk hv, hrp] at hL'
    simp only at hL'
    cases hrm : B.ns !! m with
    | none => rw [hrm] at hL'; cases hL'
    | some rm =>
    rw [hrm] at hL'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL'
    obtain ⟨hleaf, rfl⟩ := hL'
    have hnmp : B.nm !! p = some m := by rw [← hres]; exact hrp
    have hrn : B.bv.rootNode' ≠ null := by
      intro h
      have h0 : B.nm !! p = none := by rw [(hc.2.2.1 h).2]; rfl
      rw [h0] at hnmp; cases hnmp
    obtain ⟨hanc, hHq⟩ := hnode m hrp
    have hqn : ∀ q ∈ p :: H, ∃ m', resolve B q = some m' := by
      intro q hq
      rcases List.mem_cons.1 hq with h | hq'
      · rw [h]; exact ⟨m, hrp⟩
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq'
        exact ⟨_, hHq j q hj⟩
    cases hrc : resolve B c with
    | some m' =>
      have hnc : B.nm !! c = some m' := by rw [← hres]; exact hrc
      obtain ⟨-, -, hch⟩ := (hc.2.2.2.2.2.2.2.1 m rm hrm).2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      obtain ⟨r', hr', hpar⟩ := (hch _ (getD_mem rm.ws i hi)).2.1 m' (by rw [hcd]; exact hnc)
      have hm'null := (hc.2.2.2.2.1 c m' hnc).1
      have hparm : par B m' = m := by
        unfold par; rw [if_neg hm'null, hr']; simp [hpar]
      have hanc' : anc B (H.length + 1) m' = B.bv.rootNode' := by
        show anc B H.length (par B m') = _
        rw [hparm, hanc]
      have hHq' : ∀ j q, (p :: H)[j]? = some q → resolve B q = some (anc B (j + 1) m') := by
        intro j q hj
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          show resolve B p = some (anc B 0 (par B m'))
          rw [hparm]; exact hrp
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          show resolve B q = some (anc B (j + 1) (par B m'))
          rw [hparm]; exact hHq j q hj
      refine ⟨?_, hpgs', ?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd⟩
        intro hmem
        obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hmem
        have hqc : q = c := BitVec.eq_of_toNat_eq hqe
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
        have := hHq' j q hj
        rw [hqc, hrc] at this
        injection this with he
        have e1 : anc B (H.length + 1) m' = anc B (j + 1) B.bv.rootNode' := by
          have e0 : anc B (H.length + 1) m' = anc B (H.length + 1) (anc B (j + 1) m') := by
            rw [← he]
          rw [e0, ← anc_add, Nat.add_comm, anc_add, hanc']
        have e2 : anc B (j + 1) B.bv.rootNode' = null := by
          show anc B j (par B _) = null
          rw [par_root X bl B bnd hwm hB hc hbk hv, anc_null]
        exact hrn (by rw [← hanc', e1, e2])
      · intro m'' hm''
        rw [hrc] at hm''; cases hm''
        rw [List.length_cons]
        exact ⟨hanc', hHq'⟩
      · intro h; rw [hrc] at h; cases h
    | none =>
      have hfree : ∀ d, treeHas X.v.pages c.toNat d → B.nm !! W64 (d : Int) = none := by
        rcases hcI with ⟨m', -, hm', -⟩ | ⟨-, -, hf⟩ | ⟨-, h0, -⟩
        · rw [hrc] at hm'; cases hm'
        · exact hf
        · exact absurd h0 hin
      have hnotq : ∀ q ∈ p :: H, ¬ treeHas X.v.pages c.toNat q.toNat := by
        intro q hq ht
        obtain ⟨m'', hm''⟩ := hqn q hq
        have := hfree _ ht
        rw [w64_toNat_eq, ← hres, hm''] at this; cases this
      refine ⟨hnd_of hnotq, hpgs', ?_, ?_⟩
      · intro m'' h; rw [hrc] at h; cases h
      · intro _ q hq; exact hnotq q hq
  | none =>
    have hp2 : B.ib.root' ≠ W64 0 ∧ treeKeys X.v.pages p.toNat b.1 b.2 ∧
        ∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none := by
      rcases hI with ⟨m, -, hm, -⟩ | h | ⟨-, h0, -⟩
      · rw [hrp] at hm; cases hm
      · exact h
      · exact absurd h0 hin
    obtain ⟨-, htk, hfp⟩ := hp2
    obtain ⟨pg, hpg⟩ := treeKeys_some _ _ _ _ htk
    have hL' := hL
    rw [pageL_ltree X bl B bnd hwm hB hc hbk hv p hin hfp pg hpg] at hL'
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL'
    obtain ⟨hfl, rfl⟩ := hL'
    have hbf : pageFlags pg = branchPageFlag := by
      rcases (Read.viewWF_page X.v hv _ pg hpg).2.2.2 with h | h
      · exact h
      · exact absurd h hfl
    rw [pageWs_len] at hi
    have hcdef : c.toNat = branchPgid pg i := by
      rw [← hcd, pageWs_getD pg i hi, (pageW_branch pg i hfl).2, branchPgid_toNat]
    have hsub : ∀ d, treeHas X.v.pages c.toNat d → treeHas X.v.pages p.toNat d := by
      intro d hd; rw [hcdef] at hd; exact treeHas.sub _ pg d hpg (pageHas.child pg i d hbf hi hd)
    have hnotp : ¬ treeHas X.v.pages c.toNat p.toNat := by
      rw [hcdef]; exact ((viewWF_unique X.v hv).1 p.toNat pg hpg hbf).2 i hi
    have hnotq : ∀ q ∈ p :: H, ¬ treeHas X.v.pages c.toNat q.toNat := by
      intro q hq ht
      rcases List.mem_cons.1 hq with h | hq'
      · rw [h] at ht; exact hnotp ht
      · exact hpage hrp q hq' (hsub _ ht)
    have hrc : resolve B c = none := by
      rw [hres]
      obtain ⟨cpg, hcpg'⟩ := Option.isSome_iff_exists.1 hcpg
      have := hfp _ (hsub _ (treeHas.root _ cpg hcpg'))
      rwa [w64_toNat_eq] at this
    refine ⟨hnd_of hnotq, hpgs', ?_, ?_⟩
    · intro m'' h; rw [hrc] at h; cases h
    · intro _ q hq; exact hnotq q hq

/-- **A route ends at a leaf of the walk** (a file bucket): within the fuel left, with the
bounds the walk gives it holding the key. -/
theorem walk (hin : B.ib.root' ≠ W64 0) (k : List w8) : ∀ (rest H : List w64) (p : w64)
    (b : Bnd) (f : Nat), lRoute (ltree X) bl k (p :: rest) → hInv X B H p →
    bInvL X B bnd p b → keyIn b.1 b.2 k → X.v.pages.size < f + H.length →
    ∃ b' ws, ltree X bl ((p :: rest).getLast (List.cons_ne_nil _ _)) = some (true, ws) ∧
      ((p :: rest).getLast (List.cons_ne_nil _ _), b', ws) ∈ lleavesB (ltree X) bl f p b ∧
      bInvL X B bnd ((p :: rest).getLast (List.cons_ne_nil _ _)) b' ∧ keyIn b'.1 b'.2 k
  | [], H, p, b, f, hr, hH, hI, hk, hf => by
    obtain ⟨ws, hL⟩ := hr
    have := hInv_len X bl B bnd hwm hB hc hbk hv H p hH
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    refine ⟨b, ws, hL, ?_, hI, hk⟩
    simp [lleavesB, hL]
  | q :: rest, H, p, b, f, hr, hH, hI, hk, hf => by
    obtain ⟨ws, i, hL, hi, h0, h1, hq, hr'⟩ := hr
    have hlen := hInv_len X bl B bnd hwm hB hc hbk hv H p hH
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hch := (bInvL_branch X bl B bnd hwm hB hc hbk hv p b hI ws hL).2.2 i hi
    have hk' := route_keyIn b ws k hk i h0 h1
    have hH' := hInv_step X bl B bnd hwm hB hc hbk hv hin H p b hH hI ws hL i hi q hq
    obtain ⟨b', ws', hL', hmem, hI', hk''⟩ := walk hin k rest (p :: H) q (wEntryBnd b ws i) f hr'
      hH' (hq ▸ hch) hk' (by simp only [List.length_cons]; omega)
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    refine ⟨b', ws', hL', ?_, hI', hk''⟩
    simp only [lleavesB, hL]
    rw [List.mem_flatMap]
    exact ⟨i, List.mem_range.2 hi, by rw [hq]; exact hmem⟩

/-- **A route from the root ends at a block of the bucket's walk**, whose bounds hold the key. -/
theorem route_main (k : List w8) (pids : List w64) (hr : lRoute (ltree X) bl k pids)
    (hh : pids.head? = some (X.rootPid bl)) :
    ∃ last b' ws, pids.getLast? = some last ∧ ltree X bl last = some (true, ws) ∧
      (last, b', ws) ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none) ∧
      bInvL X B bnd last b' ∧ keyIn b'.1 b'.2 k := by
  cases pids with
  | nil => cases hh
  | cons p rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    by_cases hin : B.ib.root' = W64 0
    · cases rest with
      | cons q rest =>
        obtain ⟨ws, _, hL, -⟩ := hr
        exact absurd hL (inl_noBranch X bl B bnd hwm hB hc hbk hv hin _ ws)
      | nil =>
        obtain ⟨ws, hL⟩ := hr
        refine ⟨_, (none, none), ws, rfl, hL, ?_, bInvL_root X bl B bnd hwm hB hc hbk hv,
          keyIn_none k⟩
        rw [show X.fuel = (X.v.pages.size + X.t.bs.size) + 1 from rfl]
        simp [lleavesB, hL]
    · obtain ⟨b', ws, hL, hmem, hI, hk⟩ := walk X bl B bnd hwm hB hc hbk hv hin k rest []
        (X.rootPid bl) (none, none) X.fuel hr (hInv_root X bl B bnd hwm hB hc hbk hv hin)
        (bInvL_root X bl B bnd hwm hB hc hbk hv) (keyIn_none k)
        (by simp only [List.length_nil, WX.fuel]; omega)
      exact ⟨_, b', ws, List.getLast?_eq_getLast (List.cons_ne_nil _ _), hL, hmem, hI, hk⟩

end lroutes

/-! ## Stacks are routes -/

section stacks
variable [GooseExts]

/-- A logical stack routing `k` is a route of `k`. -/
theorem lRoute_of (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) (k : List w8)
    (hp : lPath X bl els pids) (hr : lRoutes X bl els pids k) : lRoute (ltree X) bl k pids := by
  obtain ⟨hne, hlen, -, hstep⟩ := hp
  have key : ∀ m j, j + m + 1 = pids.length → lRoute (ltree X) bl k (pids.drop j) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      have hj' : j < pids.length := by omega
      have hje : j < els.length := by omega
      obtain ⟨-, lf, ws, hL, -, hlast⟩ := hstep j els[j] pids[j]
        (List.getElem?_eq_getElem hje) (List.getElem?_eq_getElem hj')
      rw [List.drop_eq_getElem_cons hj', List.drop_eq_nil_of_le (by omega)]
      exact ⟨ws, by rw [hL, hlast (by omega)]⟩
    | succ m ih =>
      intro j hj
      have hj' : j < pids.length := by omega
      have hj1 : j + 1 < pids.length := by omega
      have hje : j < els.length := by omega
      obtain ⟨-, lf, ws, hL, hnext, -⟩ := hstep j els[j] pids[j]
        (List.getElem?_eq_getElem hje) (List.getElem?_eq_getElem hj')
      obtain ⟨hlf, w, hw, hpn⟩ := hnext (by omega)
      subst hlf
      obtain ⟨hi, h0, h1⟩ := (hr j els[j] pids[j] false ws (List.getElem?_eq_getElem hje)
        (List.getElem?_eq_getElem hj') hL).1 rfl
      have hgd : ws.getD els[j].index'.toNat default = w := by
        rw [List.getD_eq_getElem?_getD, hw]; rfl
      have ih' := ih (j + 1) (by omega)
      rw [List.drop_eq_getElem_cons hj1] at ih'
      rw [List.drop_eq_getElem_cons hj', List.drop_eq_getElem_cons hj1]
      refine ⟨ws, els[j].index'.toNat, hL, hi, ?_, ?_, ?_, ih'⟩
      · rcases h0 with h | ⟨w', hw', hlt⟩
        · exact Or.inl h
        · right; rw [List.getD_eq_getElem?_getD, hw']; exact hlt
      · intro h
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        exact h1 _ (List.getElem?_eq_getElem h)
      · rw [hgd]
        rw [List.getElem?_eq_getElem hj1] at hpn
        exact (Option.some.inj hpn).symm
  have hpos : pids.length ≠ 0 := by
    rw [hlen]; intro h; exact hne (List.eq_nil_of_length_eq_zero h)
  have := key (pids.length - 1) 0 (by omega)
  simpa using this

end stacks

end LR

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write LR in
/-- **`lRoutes_found`** (`Model/WOps`), proved: on a searchable bucket, a stack routing `k` ends
at the leaf entry of key `k` if the bucket has one, and at no entry of key `k` otherwise. -/
theorem lRoutes_found' [GooseExts] (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64)
    (k : List w8) (hb : bktLocalOK X bl) (hp : lPath X bl els pids) (hr : lRoutes X bl els pids k) :
    (∃ w ∈ X.allEnts bl, w.key = k) ↔ wsFound (lLeaf X bl pids) k := by
  obtain ⟨-, B, hB, hc, ⟨bnd, hbk⟩, -, -, hv⟩ := hb
  have hR := LR.lRoute_of X bl els pids k hp hr
  obtain ⟨last, b', ws, hgl, hL, hmem, hI, hk⟩ :=
    LR.route_main X bl B bnd _ hB hc hbk hv k pids hR hp.2.2.1
  have hleaf : lLeaf X bl pids = ws := by unfold lLeaf; rw [hgl]; simp only [hL]
  rw [hleaf]
  have hs := (LR.bInvL_leaf X bl B bnd _ hB hc hbk hv last b' hI ws hL).1
  have hwalk := LR.bInvL_walk X bl B bnd _ hB hc hbk hv X.fuel _ _
    (LR.bInvL_root X bl B bnd _ hB hc hbk hv)
  have hall : X.allEnts bl =
      ((lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none)).map fun x => x.2.2).flatten := by
    unfold WX.allEnts WX.leaves; rw [lleavesB_snd]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hall, List.mem_flatten] at hw
    obtain ⟨l, hl, hwl⟩ := hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have hkx := hwalk.1 x hx w hwl
    have hxy : x = (last, b', ws) := by
      apply Classical.byContradiction
      intro hne
      have := pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hwalk.2.1 x hx _ hmem hne
      exact this w.key hkx hk
    subst hxy
    exact LR.wsFound_of_mem ws hs w hwl
  · intro hf
    unfold wsFound at hf
    cases hw : ws[wsIdx ws k]? with
    | none => rw [hw] at hf; cases hf
    | some w =>
      rw [hw] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      refine ⟨w, ?_, hf⟩
      rw [hall, List.mem_flatten]
      exact ⟨ws, List.mem_map.2 ⟨_, hmem, rfl⟩, List.mem_of_getElem? hw⟩

end bbolt
end EtcdGrove
end Perennial
