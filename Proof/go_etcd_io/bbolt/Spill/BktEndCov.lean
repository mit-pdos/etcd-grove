/-
`Bucket.spill`'s root loop's end (U9x8, `notes/bbolt-proof-plan.md`): **an unspilled tree owns
every slot its bucket's logical tree covers** (`uTree_cov`, the converse of `Spill/BktSlotCov`'s
`uTree_pieces`). From a node `n` at position `pid` (`resolve`), a slot in the extent of a position
of the walk from `pid` (`posCov`: a node's own page, or a page under a page position), or of a
page of a nested bucket of one of its leaves (`leafCov`), is a slot `D` of `n`'s unspilled tree:
a node's page is its `ownSl`; a page under a page position is a page of the entry's finished tree
(`fTree`, whose `sTree` holds every page the position's subtree reaches, nested buckets
included); a nested bucket of a leaf node is its `bvalS` slots `Sb`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov
public import Proof.go_etcd_io.bbolt.Spill.STreeBuild
public import Proof.go_etcd_io.bbolt.Spill.TreeAgree
public import Proof.go_etcd_io.bbolt.Spill.BktPlain
public import Proof.go_etcd_io.bbolt.Spill.BktEls
public import Proof.go_etcd_io.bbolt.Rebalance.RblMat
public import Proof.go_etcd_io.bbolt.Spill.BktRootPos

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section cov
variable [GooseExts]

/-- Slot `s` is in the extent of a position of the walk of `bl` from `pid` (fuel `k`). -/
def posCov (X : WX) (bl : Loc) (k : Nat) (pid : w64) (s : Nat) : Prop :=
  ∃ q ∈ lposF (ltree X) bl k pid, ∃ e, X.posExtent bl q = some e ∧ e.1.toNat ≤ s ∧
    s < e.1.toNat + e.2

/-- Slot `s` is in the extent of a page of a nested bucket of a leaf of the walk of `bl` from
`pid` (fuel `k`). -/
def leafCov (X : WX) (bl : Loc) (k : Nat) (pid : w64) (s : Nat) : Prop :=
  ∃ ws ∈ lleaves (ltree X) bl k pid, ∃ w ∈ ws, isBktFlag w.flags ∧
    bucketCovers X.v.pages w.value s

/-- What the walk of `bl` covers from `pid`. -/
def walkCov (X : WX) (bl : Loc) (k : Nat) (pid : w64) (s : Nat) : Prop :=
  posCov X bl k pid s ∨ leafCov X bl k pid s

theorem isBkt_iff (f : w32) : isBktFlag f ↔ f.toNat % 2 = 1 := by
  have := notBkt_iff f
  constructor
  · intro h
    exact Classical.byContradiction fun hc => (this.2 (by omega)) h
  · intro h
    exact Classical.byContradiction fun hn => by have := this.1 hn; omega

/-- **Below an unmaterialized position, the walk covers its subtree's pages.** -/
theorem walkCov_pages {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) {hwm : Nat} :
    ∀ k p, treeWF X.v.pages hwm p.toNat →
      (∀ d, treeHas X.v.pages p.toNat d → B.nm !! W64 (d : Int) = none) → ∀ s, walkCov X bl k p s →
      ∃ id pg, treeHas X.v.pages p.toNat id ∧ X.v.pages !! id = some pg ∧ id ≤ s ∧
        s < id + (1 + pageOverflow pg)
  | 0, p, _, _, s, h => by
    rcases h with ⟨q, hq, -⟩ | ⟨ws, hws, -⟩
    · simp [lposF] at hq
    · simp [lleaves] at hws
  | k + 1, p, hwf, hfree, s, h => by
    obtain ⟨pg, hpg⟩ := treeWF_page_some hwf
    have hroot : treeHas X.v.pages p.toNat p.toNat := treeHas.root _ pg hpg
    have hnm : B.nm !! p = none := by
      have := hfree _ hroot; rwa [w64_toNat_cast] at this
    have hL := ltree_unmat X bl B hB h0 p hnm pg hpg
    obtain ⟨-, -, hpt⟩ := mat_ptwf hwf hpg
    rcases mat_kind hpt with ⟨hlf, -, -⟩ | ⟨hbr, -, hch⟩
    · -- a leaf page
      have hd : decide (pageFlags pg = leafPageFlag) = true := by simp [hlf]
      rw [hd] at hL
      rcases h with ⟨q, hq, e, he, h1, h2⟩ | ⟨ws, hws, w, hw, hbk, id, ipg, hid, hipg, h1, h2⟩
      · simp only [lposF, hL, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        have hp0 : q ≠ W64 0 := by
          intro e0; subst e0; simp only [WX.posExtent, hB, resolve, h0, ↓reduceIte, hnm] at he
          simp at he
        simp only [WX.posExtent, hB, resolve, h0, ↓reduceIte, hnm, hp0, hpg,
          Option.map_some, Option.some.injEq] at he
        subst he
        exact ⟨q.toNat, pg, hroot, hpg, h1, h2⟩
      · simp only [lleaves, hL, List.mem_singleton] at hws
        subst hws
        obtain ⟨i, hi, rfl⟩ := mem_pageWs pg w hw
        have hw' : pageW pg i = ⟨W32 (leafFlags pg i : Int), W64 0, leafKey pg i, leafValue pg i,
            Src.view, Src.view⟩ := by simp [pageW, hlf]
        rw [hw'] at hbk hid
        have hbf : leafFlags pg i % 2 = bucketLeafFlag := by
          have := (isBkt_iff _).1 hbk
          have hl := leafFlags_lt pg i
          have e : (W32 (leafFlags pg i : Int)).toNat = leafFlags pg i := by
            simp only [BitVec.toNat_ofInt]; omega
          rw [e] at this
          unfold bucketLeafFlag
          omega
        exact ⟨id, ipg, treeHas_bucket hpg hlf hi hbf hid, hipg, h1, h2⟩
    · -- a branch page
      have hd : decide (pageFlags pg = leafPageFlag) = false := by
        simp [hbr, branchPageFlag, leafPageFlag]
      rw [hd] at hL
      have hsub : ∀ w ∈ pageWs pg, treeWF X.v.pages hwm w.pgid.toNat ∧
          ∀ d, treeHas X.v.pages w.pgid.toNat d → treeHas X.v.pages p.toNat d := by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := mem_pageWs pg w hw
        rw [pageW_pgid_branch pg i hbr, branchPgid_cast]
        exact ⟨hch i hi, fun d hd => treeHas_child hpg hbr hi hd⟩
      rcases h with ⟨q, hq, e, he, h1, h2⟩ | ⟨ws, hws, w', hw', hbk, hc⟩
      · simp only [lposF, hL, List.mem_cons] at hq
        rcases hq with rfl | hq
        · have hp0 : q ≠ W64 0 := by
            intro e0; subst e0; simp only [WX.posExtent, hB, resolve, h0, ↓reduceIte, hnm] at he
            simp at he
          simp only [WX.posExtent, hB, resolve, h0, ↓reduceIte, hnm, hp0, hpg,
            Option.map_some, Option.some.injEq] at he
          subst he
          exact ⟨q.toNat, pg, hroot, hpg, h1, h2⟩
        · obtain ⟨w, hw, hqw⟩ := List.mem_flatMap.1 hq
          obtain ⟨hwf', hsub'⟩ := hsub w hw
          obtain ⟨id, ipg, ht, hipg, a1, a2⟩ := walkCov_pages hB h0 k w.pgid hwf'
            (fun d hd => hfree d (hsub' d hd)) s (Or.inl ⟨q, hqw, e, he, h1, h2⟩)
          exact ⟨id, ipg, hsub' id ht, hipg, a1, a2⟩
      · simp only [lleaves, hL] at hws
        obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
        obtain ⟨hwf', hsub'⟩ := hsub w hw
        obtain ⟨id, ipg, ht, hipg, a1, a2⟩ := walkCov_pages hB h0 k w.pgid hwf'
          (fun d hd => hfree d (hsub' d hd)) s (Or.inr ⟨ws, hws', w', hw', hbk, hc⟩)
        exact ⟨id, ipg, hsub' id ht, hipg, a1, a2⟩

/-- A slot in the extent of a page of `S` is a slot of `pgSlots`. -/
theorem mem_pgSlots_of {P : Pages} {S : List Nat} {x : Nat} (hx : x ∈ S) {pg : List w8}
    (hpg : P !! x = some pg) {s : Nat} (h1 : x ≤ s) (h2 : s < x + (1 + pageOverflow pg)) :
    s ∈ pgSlots P S := by
  unfold pgSlots
  refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
  rw [hpg]
  simp only [List.mem_range']
  exact ⟨s - x, by omega, by omega⟩

/-- A node's own page's extent is its `ownSl`. -/
theorem posExtent_node_ownSl {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    {pid : w64} {n : Loc} {r : NRec} (hres : resolve B pid = some n) (hr : B.ns !! n = some r)
    {e : w64 × Nat} (he : X.posExtent bl pid = some e) {s : Nat} (h1 : e.1.toNat ≤ s)
    (h2 : s < e.1.toNat + e.2) : s ∈ ownSl X.v r.nv.pgid' := by
  simp only [WX.posExtent, hB, hres, hr, Option.map_some, Option.getD_some] at he
  by_cases h0 : r.nv.pgid' = W64 0
  · simp [h0] at he
  · simp only [h0, ↓reduceIte] at he
    cases hpg : X.v.pages !! r.nv.pgid'.toNat with
    | none => rw [hpg] at he; cases he
    | some pg =>
      rw [hpg] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      unfold ownSl
      rw [if_neg h0]
      exact mem_pgSlots_of List.mem_cons_self hpg h1 h2

/-- **An unspilled tree owns what its bucket's walk covers** (see the module doc). -/
theorem uTree_cov {X : WX} {bl : Loc} {B : BRec} {hwm' : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm' bl B) {P : Pages} (hag : pagesLe X.v.pages P) {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ k pid, resolve B pid = some n → ∀ s, walkCov X bl k pid s → s ∈ D :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n _ _ _ _ D _ _ _ =>
      ∀ k pid, resolve B pid = some n → ∀ s, walkCov X bl k pid s → s ∈ D)
    (motive_2 := fun n _ _ _ _ _ i w e _ => B.ib.root' ≠ W64 0 →
      (e.ch = none → pagePosAt B n i w.pgid) → ∀ k s, walkCov X bl k w.pgid s → s ∈ e.D)
    (fun n r _ _ Sb hnode _ hleaf _ hsb _ => by
      intro k pid hres s hcov
      have hr := node_ns hB hnode
      have hL : ltree X bl pid = some (true, r.ws) := by
        simp only [ltree, hB, hres, hr, Option.map_some, hleaf]
      cases k with
      | zero =>
        rcases hcov with ⟨q, hq, -⟩ | ⟨ws, hws, -⟩
        · simp [lposF] at hq
        · simp [lleaves] at hws
      | succ k =>
        rcases hcov with ⟨q, hq, e, he, h1, h2⟩ | ⟨ws, hws, w, hw, hbk, id, pg, hid, hpg, h1, h2⟩
        · simp only [lposF, hL, List.mem_cons, List.not_mem_nil, or_false] at hq
          subst hq
          exact List.mem_append_left _ (posExtent_node_ownSl hB hres hr he h1 h2)
        · simp only [lleaves, hL, List.mem_singleton] at hws
          subst hws
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
          have hb := hsb i _ (List.getElem?_eq_getElem hi) hbk
          have hS := (bvalS_has hb id).1 (bucketHas_le hag hid)
          refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩)
          exact mem_pgSlots_of hS (hag id pg hpg) h1 h2)
    (fun n r _ _ _ es hnode _ hleaf _ hlen hent _ hcsE _ _ _ ih => by
      intro k pid hres s hcov
      have hr := node_ns hB hnode
      have h0 : B.ib.root' ≠ W64 0 := by
        intro e; have := hcl.2.2.2.2.2.2.1 e n r hr; rw [hleaf] at this; cases this
      have hL : ltree X bl pid = some (false, r.ws) := by
        simp only [ltree, hB, hres, hr, Option.map_some, hleaf]
      cases k with
      | zero =>
        rcases hcov with ⟨q, hq, -⟩ | ⟨ws, hws, -⟩
        · simp [lposF] at hq
        · simp [lleaves] at hws
      | succ k =>
        have hsub : ∀ w ∈ r.ws, ∀ s, walkCov X bl k w.pgid s → s ∈ es.flatMap UE.D := by
          intro w hw s hc
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
          have hwi : r.ws[i]? = some r.ws[i] := List.getElem?_eq_getElem hi
          have hi' : i < es.length := by omega
          have hei : es[i]? = some es[i] := List.getElem?_eq_getElem hi'
          have := ih i _ _ hwi hei h0 (fun hch => ⟨r, r.ws[i], hr, hleaf, hwi, rfl,
            fin_unmat hcl hB hr hleaf hlen hent hcsE hwi hei hch⟩) k s hc
          exact List.mem_flatMap.2 ⟨_, List.getElem_mem hi', this⟩
        rcases hcov with ⟨q, hq, e, he, h1, h2⟩ | ⟨ws, hws, w', hw', hbk, hc⟩
        · simp only [lposF, hL, List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact List.mem_append_left _ (posExtent_node_ownSl hB hres hr he h1 h2)
          · obtain ⟨w, hw, hqw⟩ := List.mem_flatMap.1 hq
            exact List.mem_append_right _ (hsub w hw s (Or.inl ⟨q, hqw, e, he, h1, h2⟩))
        · simp only [lleaves, hL] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          exact List.mem_append_right _ (hsub w hw s (Or.inr ⟨ws, hws', w', hw', hbk, hc⟩)))
    (fun _ _ _ _ _ _ _ w c rc _ _ _ _ _ hnode _ hpg _ _ _ _ ih => by
      intro h0 _ k s hcov
      have hr := node_ns hB hnode
      have hnm : B.nm !! rc.nv.pgid' = some c := (hcl.2.2.2.2.2.2.2.1 c rc hr).2.2.2.2.2.2.2.1
      rw [hpg] at hnm
      have hres : resolve B w.pgid = some c := by unfold resolve; rw [if_neg h0]; exact hnm
      exact ih k w.pgid hres s hcov)
    (fun n _ _ _ _ _ i w S _ hfT => by
      intro h0 hpp k s hcov
      have hpp := hpp rfl
      have hpr : posRoot B w.pgid.toNat :=
        Or.inr ⟨n, i, by rw [w64_toNat_cast]; exact hpp, w.pgid.isLt⟩
      have hwf := posRoot_treeWF hcl hpr
      have hfree : ∀ d, treeHas X.v.pages w.pgid.toNat d → B.nm !! W64 (d : Int) = none :=
        fun d hd => hcl.2.2.2.2.2.2.2.2.2.1 n i w.pgid hpp d hd
      obtain ⟨id, pg, ht, hpg, h1, h2⟩ := walkCov_pages hB h0 k w.pgid hwf hfree s hcov
      have hS : id ∈ S := (hfT.1.has id).1 (treeHas_le hag ht)
      exact mem_pgSlots_of hS (hag id pg hpg) h1 h2)
    hu

/-- The root position resolves to the root node. -/
theorem resolve_rootPid {X : WX} {bl : Loc} {B : BRec} {hwm' : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm' bl B) (hrn : B.bv.rootNode' ≠ null) :
    resolve B (X.rootPid bl) = some B.bv.rootNode' := by
  have hp : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  rw [hp]
  unfold resolve
  by_cases h0 : B.ib.root' = W64 0
  · rw [if_pos h0, if_neg hrn]
  · rw [if_neg h0]; exact hcl.2.2.2.1 hrn

/-- **A bucket's unspilled tree from its root node owns every slot its positions cover.** -/
theorem uTree_coverW {X : WX} {bl : Loc} {B : BRec} {hwm' : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm' bl B) (hrn : B.bv.rootNode' ≠ null) {P : Pages}
    (hag : pagesLe X.v.pages P) {hwm : Nat} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm B.bv.rootNode' lo hi h F D N E) {s : Nat} {pid : w64}
    (hc : coverW X s (.pos bl pid)) : s ∈ D := by
  obtain ⟨-, hp, e, he, h1, h2⟩ := hc
  exact uTree_cov hB hcl hag hu X.fuel _ (resolve_rootPid hB hcl hrn) s
    (Or.inl ⟨pid, hp, e, he, h1, h2⟩)

/-- **A bucket's unspilled tree from its root node owns every slot of its leaves' nested
buckets.** -/
theorem uTree_leafCov {X : WX} {bl : Loc} {B : BRec} {hwm' : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm' bl B) (hrn : B.bv.rootNode' ≠ null) {P : Pages}
    (hag : pagesLe X.v.pages P) {hwm : Nat} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm B.bv.rootNode' lo hi h F D N E) {ws : List WEntry}
    (hws : ws ∈ X.leaves bl) {w : WEntry} (hw : w ∈ ws) (hbk : isBktFlag w.flags) {s : Nat}
    (hc : bucketCovers X.v.pages w.value s) : s ∈ D :=
  uTree_cov hB hcl hag hu X.fuel _ (resolve_rootPid hB hcl hrn) s
    (Or.inr ⟨ws, hws, w, hw, hbk, hc⟩)

end cov

end Spill

end bbolt
end EtcdGrove
end Perennial
