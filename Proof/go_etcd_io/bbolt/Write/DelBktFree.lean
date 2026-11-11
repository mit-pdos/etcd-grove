/-
U7p (`notes/bbolt-proof-plan.md`): **`child.free()`'s premises** (`dbk_freePre`, for
`Write/DelBktWp`). The child `c` (record `C`, a root page) is a bucket of the writer's records:
- its logical tree is finite (`rtOK_init`) and has the shape of its view page tree (`pltree`: a
  materialized node is read from its page, a branch keeps its page's children, `nodePg`;
  `ltree_pltree`), so the view tree is a finite tree `t` (`ltIs_tr`) with the bucket's positions;
- `t`'s positions are distinct (`pl_nodup`: no page is shared, `viewUnique`), so are their pages'
  slots (`pagesDisjoint`);
- each slot is covered by `c`'s extents, so not pending (`flView`), not free and its first page
  allocated before the view (`mvccView`): the extents can be freed in order
  (`canFreeAll_of_disj`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktFreeFl
public import Proof.go_etcd_io.bbolt.Write.WalkDeadDefs
public import Proof.go_etcd_io.bbolt.Write.FlView
public import Proof.go_etcd_io.bbolt.Write.Free
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Read.TreeFacts
public import Proof.go_etcd_io.bbolt.Read.LRoutes

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section free
variable [GooseExts]

/-- **The view tree and the logical tree of a bucket with a root page have one shape.** -/
theorem ltree_pltree (X : WX) (hok : wOK X) (c : Loc) (C : BRec) (hC : X.t.bs !! c = some C)
    (h0 : C.ib.root' ≠ W64 0) (q : w64) :
    (pltree X.v c q).map Prod.fst = (ltree X c q).map Prod.fst ∧
      shp (pltree X.v c q) = shp (ltree X c q) := by
  have hc := (hok.1.2.2.2.2.2 c C hC).1
  cases hq : C.nm !! q with
  | none =>
    cases hp : X.v.pages !! q.toNat with
    | none =>
      have h1 : pltree X.v c q = none := by unfold pltree; rw [hp]; rfl
      have h2 : ltree X c q = none := by
        simp only [ltree, hC, resolve, h0, ↓reduceIte, hq, wpageAt, hp, Option.map_none]
      rw [h1, h2]; exact ⟨rfl, rfl⟩
    | some pg =>
      have h1 : pltree X.v c q = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
        unfold pltree; rw [hp]; rfl
      rw [h1, ltree_unmat X c C hC h0 q hq pg hp]; exact ⟨rfl, rfl⟩
  | some l =>
    obtain ⟨-, r, hr, hpid⟩ := hc.2.2.2.2.1 q l hq
    rw [ltree_mat X c C hC h0 q l r hq hr]
    obtain ⟨hpl, hpb⟩ := hok.2.2.1 c C hC l r hr
    rw [hpid] at hpl hpb
    cases hleaf : r.nv.isLeaf' with
    | true =>
      obtain ⟨pg, hpg, hfl⟩ := (hpl hleaf).2 h0
      have h1 : pltree X.v c q = some (true, pageWs pg) := by
        unfold pltree; rw [hpg]; simp [hfl]
      rw [h1]; exact ⟨rfl, rfl⟩
    | false =>
      obtain ⟨-, pg, hpg, hfb, hlen, hws⟩ := hpb hleaf
      have hne : pageFlags pg ≠ leafPageFlag := by rw [hfb]; decide
      have h1 : pltree X.v c q = some (false, pageWs pg) := by
        unfold pltree; rw [hpg]; simp [hne]
      rw [h1]
      refine ⟨rfl, ?_⟩
      simp only [shp, Option.some.injEq]
      apply List.ext_getElem
      · simp [pageWs, hlen]
      · intro i h1 h2
        simp only [List.getElem_map]
        have hi : i < pageCount pg := by simpa [pageWs] using h1
        rw [hws i r.ws[i] (List.getElem?_eq_getElem (by simpa using h2))]
        simp only [pageWs, List.getElem_map, List.getElem_range]
        exact pageW_pgid_branch pg i hfb

mutual
/-- **A tree of `L` is a tree of `L'`** with the same positions and height, when `L'` has `L`'s
kinds and branch children. -/
theorem ltIs_tr (L L' : LTree) (bl : Loc)
    (hag : ∀ q, (L' bl q).map Prod.fst = (L bl q).map Prod.fst ∧ shp (L' bl q) = shp (L bl q)) :
    ∀ t, ltIs L bl t → ∃ t', ltIs L' bl t' ∧ t'.pid = t.pid ∧ t'.pos = t.pos ∧ t'.ht = t.ht
  | .mk p true ws cs, h => by
    simp only [ltIs] at h
    obtain ⟨h1, -⟩ := hag p
    rw [h.1] at h1
    cases e : L' bl p with
    | none => rw [e] at h1; cases h1
    | some y =>
      obtain ⟨b, ws'⟩ := y
      rw [e] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      refine ⟨.mk p true ws' [], ⟨e, rfl⟩, rfl, rfl, ?_⟩
      simp [RTree.ht, RTree.htL, h.2]
  | .mk p false ws cs, h => by
    simp only [ltIs] at h
    obtain ⟨h1, h2⟩ := hag p
    rw [h.1] at h1 h2
    cases e : L' bl p with
    | none => rw [e] at h1; cases h1
    | some y =>
      obtain ⟨b, ws'⟩ := y
      rw [e] at h1 h2
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      simp only [shp, Option.some.injEq] at h2
      obtain ⟨cs', a1, a2, a3⟩ := ltIsL_tr L L' bl hag ws ws' cs h.2 h2
      exact ⟨.mk p false ws' cs', ⟨e, a1⟩, rfl, by simp only [RTree.pos, a2],
        by simp only [RTree.ht, a3]⟩
theorem ltIsL_tr (L L' : LTree) (bl : Loc)
    (hag : ∀ q, (L' bl q).map Prod.fst = (L bl q).map Prod.fst ∧ shp (L' bl q) = shp (L bl q)) :
    ∀ (ws ws' : List WEntry) (cs : List RTree), ltIsL L bl ws cs →
      ws'.map WEntry.pgid = ws.map WEntry.pgid →
      ∃ cs', ltIsL L' bl ws' cs' ∧ RTree.posL cs' = RTree.posL cs ∧ RTree.htL cs' = RTree.htL cs
  | [], [], [], _, _ => ⟨[], trivial, rfl, rfl⟩
  | w :: ws, w' :: ws', t :: ts, h, hm => by
    simp only [ltIsL] at h
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨t', a1, a2, a3, a4⟩ := ltIs_tr L L' bl hag t h.2.1
    obtain ⟨cs', b1, b2, b3⟩ := ltIsL_tr L L' bl hag ws ws' ts h.2.2 hm.2
    exact ⟨t' :: cs', ⟨by rw [a2, h.1, hm.1], a1, b1⟩, by simp only [RTree.posL, a3, b2],
      by simp only [RTree.htL, a4, b3]⟩
  | [], [], _ :: _, h, _ => by simp only [ltIsL] at h
  | _ :: _, _, [], h, _ => by simp only [ltIsL] at h
  | [], _ :: _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, hm => by simp at hm
end

/-- Distinct children's subtrees. -/
def chDisj (P : Pages) (ws : List WEntry) : Prop :=
  ws.Pairwise fun w1 w2 => ∀ d, treeHas P w1.pgid.toNat d → ¬ treeHas P w2.pgid.toNat d

theorem pltree_page' (v : View) (bl : Loc) (pid : w64) (x : Bool × List WEntry)
    (h : pltree v bl pid = some x) :
    ∃ pg, v.pages !! pid.toNat = some pg ∧ x = (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  unfold pltree at h
  cases hpg : v.pages !! pid.toNat with
  | none => rw [hpg] at h; cases h
  | some pg => rw [hpg] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨pg, rfl, h.symm⟩

mutual
/-- **A view tree's positions are distinct pages of it** (no page shared). -/
theorem pl_nodup (v : View) (hv : viewWF v) (bl : Loc) :
    ∀ t, ltIs (pltree v) bl t → t.pos.Nodup ∧ ∀ x ∈ t.pos, treeHas v.pages t.pid.toNat x.toNat
  | .mk p true ws cs, h => by
    simp only [ltIs] at h
    obtain ⟨pg, hpg, -⟩ := pltree_page' v bl p _ h.1
    refine ⟨by simp [RTree.pos], ?_⟩
    intro x hx
    simp only [RTree.pos, List.mem_singleton] at hx
    subst hx
    exact treeHas.root _ pg hpg
  | .mk p false ws cs, h => by
    simp only [ltIs] at h
    obtain ⟨pg, hpg, hx⟩ := pltree_page' v bl p _ h.1
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hfl, rfl⟩ := hx
    have hne : pageFlags pg ≠ leafPageFlag := fun e => by simp [e] at hfl
    have hfb : pageFlags pg = branchPageFlag := by
      rcases (Read.viewWF_page v hv _ pg hpg).2.2.2 with e | e
      · exact e
      · exact absurd e hne
    have hu := (LR.viewWF_unique v hv).1 _ pg hpg hfb
    have hD : chDisj v.pages (pageWs pg) := by
      unfold chDisj pageWs
      rw [List.pairwise_map]
      refine (List.pairwise_lt_range (n := pageCount pg)).imp_of_mem ?_
      intro i j hi hj hij d h1 h2
      rw [List.mem_range] at hi hj
      rw [pageW_pgid_branch pg i hfb, branchPgid_cast] at h1
      rw [pageW_pgid_branch pg j hfb, branchPgid_cast] at h2
      exact hu.1 i j hi hj (by omega) d h1 h2
    obtain ⟨hnd, hin⟩ := plL_nodup v hv bl (pageWs pg) cs h.2 hD
    have hsub : ∀ x ∈ RTree.posL cs, treeHas v.pages p.toNat x.toNat ∧ x ≠ p := by
      intro x hx
      obtain ⟨w, hw, hx'⟩ := hin x hx
      obtain ⟨i, hi, rfl⟩ := mem_pageWs pg w hw
      rw [pageW_pgid_branch pg i hfb, branchPgid_cast] at hx'
      refine ⟨treeHas.sub _ pg _ hpg (pageHas.child pg i _ hfb hi hx'), ?_⟩
      rintro rfl
      exact hu.2 i hi hx'
    refine ⟨?_, ?_⟩
    · simp only [RTree.pos, List.nodup_cons]
      exact ⟨fun hm => (hsub p hm).2 rfl, hnd⟩
    · intro x hx
      simp only [RTree.pos, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact treeHas.root _ pg hpg
      · exact (hsub x hx).1
theorem plL_nodup (v : View) (hv : viewWF v) (bl : Loc) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL (pltree v) bl ws cs → chDisj v.pages ws →
      (RTree.posL cs).Nodup ∧ ∀ x ∈ RTree.posL cs, ∃ w ∈ ws, treeHas v.pages w.pgid.toNat x.toNat
  | [], [], _, _ => ⟨by simp [RTree.posL], by simp [RTree.posL]⟩
  | w :: ws, t :: ts, h, hD => by
    simp only [ltIsL] at h
    unfold chDisj at hD
    rw [List.pairwise_cons] at hD
    obtain ⟨n1, i1⟩ := pl_nodup v hv bl t h.2.1
    obtain ⟨n2, i2⟩ := plL_nodup v hv bl ws ts h.2.2 hD.2
    rw [h.1] at i1
    refine ⟨?_, ?_⟩
    · simp only [RTree.posL]
      refine List.nodup_append.2 ⟨n1, n2, ?_⟩
      rintro a ha b hb rfl
      obtain ⟨w2, hw2, h2⟩ := i2 a hb
      exact hD.1 w2 hw2 a.toNat (i1 a ha) h2
    · intro x hx
      simp only [RTree.posL, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ⟨w, List.mem_cons_self .., i1 x hx⟩
      · obtain ⟨w2, hw2, h2⟩ := i2 x hx
        exact ⟨w2, List.mem_cons_of_mem _ hw2, h2⟩
  | [], _ :: _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _ => by simp only [ltIsL] at h
end

/-- An extent of `pExt`. -/
theorem pExt_some {v : View} {p : w64} {e : w64 × Nat} (h : pExt v p = some e) :
    ∃ pg, v.pages !! p.toNat = some pg ∧ e = (p, 1 + pageOverflow pg) := by
  unfold pExt at h
  cases hp : v.pages !! p.toNat with
  | none => rw [hp] at h; cases h
  | some pg => rw [hp] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨pg, rfl, h.symm⟩

/-- **Distinct pages' runs are distinct ids.** -/
theorem extIds_nodup (P : Pages) (hd : pagesDisjoint P) (hx : pagesExt P) :
    ∀ ps : List w64, ps.Nodup → (extIds (ps.filterMap fun p =>
      (P !! p.toNat).map fun pg => (p, 1 + pageOverflow pg))).Nodup
  | [], _ => by simp [extIds]
  | p :: ps, hnd => by
    rw [List.nodup_cons] at hnd
    have ih := extIds_nodup P hd hx ps hnd.2
    cases hp : P !! p.toNat with
    | none => simp only [List.filterMap_cons, hp, Option.map_none]; exact ih
    | some pg =>
      simp only [List.filterMap_cons, hp, Option.map_some]
      have he : extIds ((p, 1 + pageOverflow pg) :: ps.filterMap fun p =>
          (P !! p.toNat).map fun pg => (p, 1 + pageOverflow pg)) =
          runIds p (1 + pageOverflow pg) ++ extIds (ps.filterMap fun p =>
          (P !! p.toNat).map fun pg => (p, 1 + pageOverflow pg)) := by
        unfold extIds; rw [List.flatMap_cons]
      rw [he]
      have hb := hx _ pg hp
      refine List.nodup_append.2 ⟨runIds_nodup (by omega), ih, ?_⟩
      rintro a ha b hb' rfl
      obtain ⟨e, he', hae⟩ := List.mem_flatMap.1 hb'
      obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.1 he'
      cases hq' : P !! q.toNat with
      | none => rw [hq'] at hqe; cases hqe
      | some pg2 =>
        rw [hq'] at hqe
        simp only [Option.map_some, Option.some.injEq] at hqe
        subst hqe
        have hb2 := hx _ pg2 hq'
        have r1 := (mem_runIds (id := p) (n := 1 + pageOverflow pg) (by omega)).1 ha
        have r2 := (mem_runIds (id := q) (n := 1 + pageOverflow pg2) (by omega)).1 hae
        have hne : p.toNat ≠ q.toNat := fun e => hnd.1 (by
          rw [show q = p from BitVec.eq_of_toNat_eq e.symm] at hq; exact hq)
        unfold inRun at r1 r2
        rcases hd _ pg _ pg2 hp hq' hne with h | h <;> omega

/-- **`child.free()`'s premises** (see the module doc): the child's tree in the view, its extents
freeable by the writer. -/
theorem dbk_freePre (X1 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (fl : FLPg) (txid : w64)
    (hok : wOK X1) (hwr : wrFacts X1) (hR1 : X1.t.bs !! X1.rl = some R1)
    (hn : R1.bm !! n = some c) (hC : X1.t.bs !! c = some C) (hfl : flViewU X1 fl)
    (htx : X1.t.mv.txid' = txid) :
    C.ib.root' ≠ W64 0 → C.bv.page' = null ∧ ∃ t : RTree, ltIs (pltree X1.v) c t ∧
      t.pid = C.ib.root' ∧ fl.canFreeAll txid (t.pos.filterMap (pExt X1.v)) := by
  intro h0
  have hc := (hok.1.2.2.2.2.2 c C hC).1
  have hvw : viewWF X1.v := hok.2.2.2.2.2.2.2
  refine ⟨hc.2.2.2.2.2.1 h0, ?_⟩
  have hrt := rtOK_init X1 c hok hvw (by rw [hC]; rfl)
  obtain ⟨t0, ht0, hp0, hh0, -⟩ := id hrt
  have hrp : X1.rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hC]; rfl
  obtain ⟨t, ht, htp, htpos, -⟩ := ltIs_tr (ltree X1) (pltree X1.v) c
    (ltree_pltree X1 hok c C hC h0) t0 ht0
  refine ⟨t, ht, by rw [htp, hp0, hrp], ?_⟩
  have hpos : X1.positions c = t.pos := by rw [positions_rt X1 c t0 ht0 hp0 hh0, htpos]
  obtain ⟨hfv, -, hpx, -⟩ := hfl
  obtain ⟨hcov, hmv, hnd, hlt62⟩ := hfv
  have htxe : X1.v.txid + 1 = txid.toNat := by rw [← htx]; exact hok.1.2.2.2.1
  have htx0 : txid ≠ W64 0 := by
    intro e; rw [e] at htxe; simp at htxe
  have hpd : pagesDisjoint X1.v.pages := by
    obtain ⟨C', hC', hvC⟩ := hvw
    rw [← hvC]; exact hC'.2.2.1
  have hext : ∀ p ∈ t.pos, ∀ e, pExt X1.v p = some e →
      ∃ pg, X1.v.pages !! p.toNat = some pg ∧ e = (p, 1 + pageOverflow pg) ∧
        2 ≤ p.toNat ∧ X1.posExtent c p = some e := by
    intro p _ e he
    obtain ⟨pg, hpg, rfl⟩ := pExt_some he
    have h2 := (Read.viewWF_page _ hvw _ pg hpg).1
    have hp0' : p ≠ W64 0 := by intro e; rw [e] at h2; simp at h2
    refine ⟨pg, hpg, rfl, h2, ?_⟩
    cases hres : resolve C p with
    | none => exact posExtent_page X1 c C p pg hC hres hp0' hpg
    | some l =>
      have hnm : C.nm !! p = some l := by unfold resolve at hres; rwa [if_neg h0] at hres
      obtain ⟨-, r, hr, hpid⟩ := hc.2.2.2.2.1 p l hnm
      exact posExtent_node X1 c C p l r pg hC hres hr hpid hp0' hpg
  apply canFreeAll_of_disj txid htx0
  · intro e he
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 he
    obtain ⟨pg, hpg, rfl, h2, -⟩ := hext p hp e hpe
    refine ⟨h2, hpx _ pg hpg, ?_⟩
    simp only
    cases ha : fl.allocs !! p with
    | none => exact fun h => htx0 h.symm
    | some a =>
      simp only [Option.getD_some]
      have := hmv.1 _ pg hpg a (by rw [w64_toNat_cast]; exact ha)
      intro e; rw [e] at this; omega
  · refine List.nodup_append.2 ⟨hnd, ?_, ?_⟩
    · exact extIds_nodup X1.v.pages hpd hpx t.pos (pl_nodup X1.v hvw c t ht).1
    · rintro a ha b hb rfl
      obtain ⟨e, he, hae⟩ := List.mem_flatMap.1 hb
      obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 he
      obtain ⟨pg, hpg, rfl, h2, hpe'⟩ := hext p hp _ hpe
      have hb62 := hpx _ pg hpg
      have r := (mem_runIds (id := p) (n := 1 + pageOverflow pg) (by omega)).1 hae
      unfold inRun at r
      have hcs : coversSlot X1.v.pages a.toNat := ⟨_, pg, hpg, r.1, r.2⟩
      have hlc : lCovers X1 a.toNat := Or.inl ⟨c, (p, 1 + pageOverflow pg), by rw [hC]; simp,
        List.mem_filterMap.2 ⟨p, by rw [hpos]; exact hp, hpe'⟩, r.1, r.2⟩
      have hnp := (hcov _ hcs).1 hlc
      have hnf := (hmv.2 _ hcs).2.1
      rw [w64_toNat_cast] at hnf
      rcases List.mem_append.1 ha with h | h
      · exact hnf h
      · exact hnp (List.mem_map_of_mem h)
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hlt62 x h
    · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 h
      obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 he
      obtain ⟨pg, hpg, rfl, -, -⟩ := hext p hp _ hpe
      have hb62 := hpx _ pg hpg
      have r := (mem_runIds (id := p) (n := 1 + pageOverflow pg) (by omega)).1 hxe
      unfold inRun at r; omega

end free

end Write

end bbolt
end EtcdGrove
end Perennial
