/-
The writer's search (U6d, `notes/bbolt-proof-plan.md`), its pure part: a position of a searchable
bucket (`posOK`: a materialized node, the inline page, or a view page whose subtree no node
materializes), stacks routing a key from a position (`lPathFrom`, `lRoutes`), and the premises
`Cursor.seek_w` needs beyond `bktLocalOK` (`pmFresh`: no view page in the transaction's page cache;
`inlSrcOK`: an inline page's bytes where its source says), with the source of a leaf entry
(`leafSrc`: an inline page's entries are its bytes', `B.isrc`, not the view's).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Read.TreeFacts
public import Spec.go_etcd_io.bbolt.Cursor__search_r

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wpos
variable [GooseExts]

-- `pmFresh`, `inlSrcOK`, `leafSrc`: moved to `Model/WOps` (batch 33, the shared `seek_w` spec's).

/-- **A logical stack from position `pid`** (`lPath` from any position). -/
def lPathFrom (X : WX) (bl : Loc) (pid : w64) (els : List elemRef) (pids : List w64) : Prop :=
  els ≠ [] ∧ pids.length = els.length ∧ pids.head? = some pid ∧
  ∀ (j : Nat) (e : elemRef) (p : w64), els[j]? = some e → pids[j]? = some p → refAt X bl p e ∧
    ∃ lf ws, ltree X bl p = some (lf, ws) ∧
      (j + 1 < els.length → lf = false ∧ ∃ w, ws[e.index'.toNat]? = some w ∧
        pids[j + 1]? = some w.pgid) ∧
      (j + 1 = els.length → lf = true)

theorem lPath_iff (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) :
    lPath X bl els pids ↔ lPathFrom X bl (X.rootPid bl) els pids := Iff.rfl

/-- **A searchable position** of bucket `bl` (record `B`): a materialized node, the inline page
(no root node), or a view page whose subtree is well-formed and has no materialized page. -/
def posOK (X : WX) (bl : Loc) (B : BRec) (pid : w64) : Prop :=
  (∃ l rn, resolve B pid = some l ∧ B.ns !! l = some rn) ∨
  (resolve B pid = none ∧ B.ib.root' = W64 0 ∧ pid = W64 0) ∨
  (B.ib.root' ≠ W64 0 ∧ treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat ∧
    ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none)

/-! ## Pages' entries -/

theorem pageWs_length (pg : List w8) : (pageWs pg).length = pageCount pg := by
  simp [pageWs]

theorem pageWs_get (pg : List w8) (i : Nat) (hi : i < pageCount pg) :
    (pageWs pg)[i]? = some (pageW pg i) := by
  simp [pageWs, hi]

theorem pageWs_get_none (pg : List w8) (i : Nat) (hi : ¬ i < pageCount pg) :
    (pageWs pg)[i]? = none := by
  simp [pageWs]; omega

theorem pageW_leaf_key (pg : List w8) (i : Nat) (h : pageFlags pg = leafPageFlag) :
    (pageW pg i).key = leafKey pg i := by
  simp [pageW, h]

theorem pageW_branch (pg : List w8) (i : Nat) (h : pageFlags pg = branchPageFlag) :
    (pageW pg i).key = branchKey pg i ∧ (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
  have : pageFlags pg ≠ leafPageFlag := by rw [h]; decide
  simp [pageW, this]

/-- The leaf page's search index is its entries'. -/
theorem pageSeekIdx_wsIdx (pg : List w8) (k : List w8) (h : pageFlags pg = leafPageFlag) :
    pageSeekIdx pg k = wsIdx (pageWs pg) k := by
  unfold pageSeekIdx wsIdx pageWs
  rw [List.takeWhile_map, List.length_map]
  congr 2
  funext i
  simp [pageW_leaf_key pg i h]

/-- A branch page's routing index gives `lRoutes`' branch clause on its entries. -/
theorem branchRoute_lroute (pg : List w8) (k : List w8) (i : Nat) (hf : pageFlags pg = branchPageFlag)
    (h : branchRoute pg k i) :
    i < (pageWs pg).length ∧
      (i = 0 ∨ ∃ w, (pageWs pg)[i]? = some w ∧ ¬ go.GoStringLt k w.key) ∧
      ∀ w, (pageWs pg)[i + 1]? = some w → go.GoStringLt k w.key := by
  obtain ⟨hi, h0, h1⟩ := h
  rw [pageWs_length]
  refine ⟨hi, ?_, ?_⟩
  · rcases h0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨_, pageWs_get pg i hi, by rw [(pageW_branch pg i hf).1]; exact h0⟩
  · intro w hw
    by_cases hlt : i + 1 < pageCount pg
    · rw [pageWs_get pg _ hlt] at hw; cases hw
      rw [(pageW_branch pg _ hf).1]; exact h1 hlt
    · rw [pageWs_get_none pg _ hlt] at hw; cases hw

/-! ## The logical tree at a position -/

theorem ltree_node (X : WX) (bl : Loc) (B : BRec) (pid : w64) (l : Loc) (rn : NRec)
    (hb : X.t.bs !! bl = some B) (hr : resolve B pid = some l) (hn : B.ns !! l = some rn) :
    ltree X bl pid = some (rn.nv.isLeaf', rn.ws) := by
  simp [ltree, hb, hr, hn]

theorem ltree_page (X : WX) (bl : Loc) (B : BRec) (pid : w64) (pa : Loc) (pg : List w8)
    (hb : X.t.bs !! bl = some B) (hr : resolve B pid = none)
    (hw : wpageAt X.v B pid = some (pa, pg)) :
    ltree X bl pid = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  simp [ltree, hb, hr, hw]

theorem refAt_node (X : WX) (bl : Loc) (B : BRec) (pid : w64) (l : Loc) (e : elemRef)
    (hb : X.t.bs !! bl = some B) (hr : resolve B pid = some l) (he : e.node' = l) :
    refAt X bl pid e := ⟨B, hb, by rw [hr]; exact he⟩

theorem refAt_page (X : WX) (bl : Loc) (B : BRec) (pid : w64) (pg : List w8) (e : elemRef)
    (hb : X.t.bs !! bl = some B) (hr : resolve B pid = none) (he : e.node' = null)
    (hw : wpageAt X.v B pid = some (e.page', pg)) :
    refAt X bl pid e := ⟨B, hb, by rw [hr]; exact ⟨he, pg, hw⟩⟩

/-! ## Stacks from a position -/

/-- A leaf position alone is a stack. -/
theorem lPathFrom_leaf (X : WX) (bl : Loc) (pid : w64) (e : elemRef) (ws : List WEntry)
    (hr : refAt X bl pid e) (hl : ltree X bl pid = some (true, ws)) :
    lPathFrom X bl pid [e] [pid] := by
  refine ⟨by simp, rfl, rfl, ?_⟩
  intro j e' p he hp
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hp
    subst he hp
    exact ⟨hr, true, ws, hl, fun h => (by simp at h), fun _ => rfl⟩
  | succ j => simp at he

/-- A branch position, then a stack from the child its index selects. -/
theorem lPathFrom_cons (X : WX) (bl : Loc) (pid : w64) (e : elemRef) (ws : List WEntry)
    (w : WEntry) (path : List elemRef) (pids : List w64)
    (hr : refAt X bl pid e) (hl : ltree X bl pid = some (false, ws))
    (hw : ws[e.index'.toNat]? = some w) (hp : lPathFrom X bl w.pgid path pids) :
    lPathFrom X bl pid (e :: path) (pid :: pids) := by
  obtain ⟨hne, hlen, hhd, hall⟩ := hp
  refine ⟨by simp, by simp [hlen], rfl, ?_⟩
  intro j e' p he hpj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hpj
    subst he hpj
    refine ⟨hr, false, ws, hl, fun _ => ⟨rfl, w, hw, ?_⟩, fun h => ?_⟩
    · cases pids with
      | nil => simp at hhd
      | cons p0 ps => simp only [List.head?_cons, Option.some.injEq] at hhd; simp [hhd]
    · cases path with
      | nil => exact absurd rfl hne
      | cons _ _ => simp at h
  | succ j =>
    simp only [List.getElem?_cons_succ] at he hpj
    obtain ⟨h1, lf, ws', h2, h3, h4⟩ := hall j e' p he hpj
    refine ⟨h1, lf, ws', h2, fun h => h3 (by simp at h; omega), fun h => h4 (by simp at h; omega)⟩

/-- `lRoutes` of a leaf alone. -/
theorem lRoutes_leaf (X : WX) (bl : Loc) (pid : w64) (e : elemRef) (ws : List WEntry) (k : List w8)
    (hl : ltree X bl pid = some (true, ws)) (hi : e.index'.toNat = wsIdx ws k) :
    lRoutes X bl [e] [pid] k := by
  intro j e' p lf ws' he hp ht
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hp
    subst he hp
    rw [hl] at ht; cases ht
    exact ⟨fun h => (by cases h), fun _ => hi⟩
  | succ j => simp at he

/-- `lRoutes` of a branch routing `k`, then a routing stack. -/
theorem lRoutes_cons (X : WX) (bl : Loc) (pid : w64) (e : elemRef) (ws : List WEntry)
    (path : List elemRef) (pids : List w64) (k : List w8)
    (hl : ltree X bl pid = some (false, ws))
    (hb : e.index'.toNat < ws.length ∧
      (e.index'.toNat = 0 ∨ ∃ w, ws[e.index'.toNat]? = some w ∧ ¬ go.GoStringLt k w.key) ∧
      ∀ w, ws[e.index'.toNat + 1]? = some w → go.GoStringLt k w.key)
    (hr : lRoutes X bl path pids k) :
    lRoutes X bl (e :: path) (pid :: pids) k := by
  intro j e' p lf ws' he hp ht
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hp
    subst he hp
    rw [hl] at ht; cases ht
    exact ⟨fun _ => hb, fun h => by cases h⟩
  | succ j =>
    simp only [List.getElem?_cons_succ] at he hp
    exact hr j e' p lf ws' he hp ht

/-! ## Searchable positions -/

theorem resolve_tree (B : BRec) (pid : w64) (h : B.ib.root' ≠ W64 0) : resolve B pid = B.nm !! pid := by
  unfold resolve; rw [if_neg h]

/-- A view page position's facts (tree case of `posOK`). -/
theorem posOK_tree_page (X : WX) (B : BRec) (pid : w64) (hr : B.ib.root' ≠ W64 0)
    (ht : treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat)
    (hnm : ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none) :
    resolve B pid = none ∧ ∃ pg, X.v.pages !! pid.toNat = some pg ∧
      wpageAt X.v B pid = some (pageLoc X.v pid.toNat, pg) ∧
      pageTreeWF X.v.pages X.t.mv.pgid'.toNat pg pg.length ∧ pageId pg = pid.toNat ∧
      pg.length = (1 + pageOverflow pg) * 4096 := by
  cases ht with
  | page _ pg h2 hlt hpg hid hlen hpt =>
    have hh : treeHas X.v.pages pid.toNat pid.toNat := treeHas.root _ pg hpg
    have := hnm _ hh
    rw [show W64 ((pid.toNat : Nat) : Int) = pid by
      apply BitVec.eq_of_toNat_eq; simp] at this
    refine ⟨by rw [resolve_tree B pid hr]; exact this, pg, hpg, ?_, hpt, hid, hlen⟩
    unfold wpageAt; rw [if_neg hr, hpg]; rfl

/-- **The root of a searchable bucket is a searchable position.** -/
theorem posOK_root (X : WX) (bl : Loc) (B : BRec) (hb : bktLocalOK X bl) (hB : X.t.bs !! bl = some B) :
    posOK X bl B B.ib.root' := by
  obtain ⟨-, B', hB', hc, -⟩ := hb
  rw [hB] at hB'; cases hB'
  by_cases hrn : B.bv.rootNode' = null
  · have hns := (hc.2.2.1 hrn)
    by_cases hi : B.ib.root' = W64 0
    · refine Or.inr (Or.inl ⟨by simp [resolve, hi, hrn], hi, hi⟩)
    · refine Or.inr (Or.inr ⟨hi, (hc.2.1 hi).2 hrn, fun d _ => by rw [hns.2]; rfl⟩)
  · by_cases hi : B.ib.root' = W64 0
    · have hres : resolve B B.ib.root' = some B.bv.rootNode' := by simp [resolve, hi, hrn]
      have hnm := hc.2.2.2.1 hrn
      obtain ⟨-, rn, hrn', -⟩ := hc.2.2.2.2.1 _ _ hnm
      exact Or.inl ⟨_, rn, hres, hrn'⟩
    · have hnm := hc.2.2.2.1 hrn
      obtain ⟨-, rn, hrn', -⟩ := hc.2.2.2.2.1 _ _ hnm
      exact Or.inl ⟨_, rn, by rw [resolve_tree B _ hi]; exact hnm, hrn'⟩

/-- **A branch node's child is a searchable position.** -/
theorem posOK_node_child (X : WX) (bl : Loc) (B : BRec) (l : Loc) (rn : NRec) (i : Nat) (w : WEntry)
    (hb : bktLocalOK X bl) (hB : X.t.bs !! bl = some B) (hn : B.ns !! l = some rn)
    (hlf : rn.nv.isLeaf' = false) (hw : rn.ws[i]? = some w) :
    posOK X bl B w.pgid := by
  obtain ⟨-, B', hB', hc, -⟩ := hb
  rw [hB] at hB'; cases hB'
  have hnc := hc.2.2.2.2.2.2.2.1 l rn hn
  have hi : B.ib.root' ≠ W64 0 := by
    intro h0
    have := hc.2.2.2.2.2.2.1 h0 l rn hn
    rw [hlf] at this; cases this
  obtain ⟨-, -, hall⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hlf
  have hwm : w ∈ rn.ws := List.mem_of_getElem? hw
  obtain ⟨-, hm, hp⟩ := hall w hwm
  cases hnm : B.nm !! w.pgid with
  | some l' =>
    obtain ⟨-, r', hr', -⟩ := hc.2.2.2.2.1 _ _ hnm
    exact Or.inl ⟨l', r', by rw [resolve_tree B _ hi]; exact hnm, hr'⟩
  | none =>
    refine Or.inr (Or.inr ⟨hi, hp hnm, fun d hd => ?_⟩)
    have hpos : pagePosAt B l i w.pgid := ⟨rn, w, hn, hlf, hw, rfl, hnm⟩
    exact hc.2.2.2.2.2.2.2.2.2.1 l i w.pgid hpos d hd

/-- **A branch page's child is a searchable position.** -/
theorem posOK_page_child (X : WX) (bl : Loc) (B : BRec) (pid : w64) (pg : List w8) (i : Nat)
    (hi : B.ib.root' ≠ W64 0) (ht : treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat)
    (hnm : ∀ d, treeHas X.v.pages pid.toNat d → B.nm !! W64 (d : Int) = none)
    (hpg : X.v.pages !! pid.toNat = some pg) (hf : pageFlags pg = branchPageFlag)
    (hic : i < pageCount pg) :
    posOK X bl B (W64 (branchPgid pg i : Int)) := by
  have hlt : branchPgid pg i < 2 ^ 64 := by unfold branchPgid; exact BitVec.isLt _
  have hc : (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
    simp; omega
  cases ht with
  | page _ pg' h2 hlt' hpg' hid hlen hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf' _ _ => rw [hf] at hf'; cases hf'
    | branch _ _ _ _ hch =>
      refine Or.inr (Or.inr ⟨hi, by rw [hc]; exact hch i hic, fun d hd => ?_⟩)
      rw [hc] at hd
      exact hnm d (treeHas.sub _ pg d hpg (pageHas.child pg i d hf hic hd))

end wpos

end bbolt
end EtcdGrove
end Perennial
