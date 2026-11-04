/-
**Materialization keeps the writer's page tokens** (batch 37 item 14; `Inv/ShapeOps`):
`nodeAdded` replaces a position's tokens (`xPages` of its page) by the new node's (its page and
its unmaterialized children's subtrees, or its leaf's unopened nested buckets' trees), a
sub-multiset by the view's uniqueness (`Inv/ShapeOpsView`); `matGrow` by induction
(`Write/MatOK.bktLocalOK_nodeAdded` for `bktLocalOK` at each step). For U7's public writes (`Cursor.node`'s
post `matGrow X X' bl`) and U6's `Bucket_w`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsView
public import Proof.go_etcd_io.bbolt.Write.MatGrow
public import Proof.go_etcd_io.bbolt.Write.FlView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.Std go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section mat
variable [GooseExts]

open Classical

theorem viewWF_unique (v : View) (h : viewWF v) : viewUnique v.pages := by
  obtain ⟨C, hC, hv⟩ := h
  rw [← hv]; exact hC.1.2.1.2

theorem treeWF_kind {P : Pages} {hwm p : Nat} {pg : List w8} (h : treeWF P hwm p)
    (hpg : P !! p = some pg) : pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag := by
  cases h with
  | page _ pg0 _ _ hpg0 _ _ hpt =>
    rw [hpg] at hpg0; cases hpg0
    cases hpt with
    | leaf _ _ hfl => exact Or.inl hfl
    | branch _ _ hfl => exact Or.inr hfl

theorem shp_isBktFlag_mod (f : Nat) (h : isBktFlag (W32 (f : Int))) : f % 2 = 1 := by
  unfold isBktFlag at h
  apply Classical.byContradiction
  intro hne
  apply h
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega

/-- The tokens of an entry depend only on its data. -/
theorem entTok_wDat (v : View) (B : BRec) (leaf : Bool) (w w' : WEntry) (h : wDat w = wDat w') :
    (if leaf = true then entTokL v B w else brTokL v B w) =
      (if leaf = true then entTokL v B w' else brTokL v B w') := by
  unfold wDat at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold entTokL brTokL
  rw [h1, h2, h3, h4]

theorem entsTokL_wDat (v : View) (B : BRec) (leaf : Bool) (ws ws' : List WEntry)
    (h : ws.map wDat = ws'.map wDat) : entsTokL v B leaf ws = entsTokL v B leaf ws' := by
  induction ws generalizing ws' with
  | nil => cases ws' with
    | nil => rfl
    | cons _ _ => cases h
  | cons w ws ih => cases ws' with
    | nil => cases h
    | cons w' ws' =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold entsTokL at ih ⊢
      simp only [List.flatMap_cons]
      rw [entTok_wDat v B leaf w w' h.1, ih ws' h.2]

/-- A node's own page tokens: at most its page. -/
theorem ownTokL_at (v : View) (r : NRec) (p : Nat) (h : r.nv.pgid'.toNat = p) :
    ownAt (ownTokL v r) p := by
  unfold ownTokL
  split
  · exact ⟨List.nodup_nil, fun _ hx => by cases hx⟩
  · refine ⟨pgIds_nodup _, fun x hx => ?_⟩
    rw [mem_filter_pgIds] at hx
    rw [of_decide_eq_true hx.2, h]

/-- **A new node's tokens**: below its position's (`xPages` of its page `p`). -/
theorem newNode_sub (v : View) (B B' : BRec) (pg : List w8) (r : NRec) (p : Nat)
    (hu : viewUnique v.pages) (hpg : v.pages !! p = some pg) (hbm : B'.bm = B.bm)
    (hrws : r.ws.map wDat = (pageWs pg).map wDat)
    (hrleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag))
    (hown : r.nv.pgid'.toNat = p)
    (hkind : pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) :
    (nodeTokL v B' r).Subperm (pgIds (xPages v.pages (opened B) p)) := by
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  unfold nodeTokL
  rw [entsTokL_wDat v B' _ r.ws (pageWs pg) hrws]
  unfold entsTokL pageWs
  rw [List.flatMap_map]
  rcases hkind with hl | hb
  · have hlf : r.nv.isLeaf' = true := by rw [hrleaf]; simp [hl]
    rw [hlf]
    refine xPages_leaf_sub v.pages (opened B) p pg hu hpg hl _ (ownTokL_at v r p hown) _ ?_
    intro i _
    simp only [↓reduceIte]
    unfold entTokL pageW
    simp only [hl, ↓reduceIte]
    rw [hop]
    split
    · rename_i hc
      exact Or.inr ⟨by unfold bucketLeafFlag; exact shp_isBktFlag_mod _ hc.1, hc.2.1, hc.2.2, rfl⟩
    · exact Or.inl rfl
  · have hne : pageFlags pg ≠ leafPageFlag := by rw [hb]; unfold branchPageFlag leafPageFlag; decide
    have hlf : r.nv.isLeaf' = false := by rw [hrleaf]; simp [hne]
    rw [hlf]
    refine xPages_branch_sub v.pages (opened B) p pg hu hpg hb _ (ownTokL_at v r p hown) _ ?_
    intro i _
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold brTokL pageW
    simp only [hne, ↓reduceIte]
    rw [hop]
    split
    · refine Or.inr ?_
      have : (W64 ((branchPgid pg i : Nat) : Int)).toNat = branchPgid pg i := by
        have := Write.branchPgid_lt pg i
        rw [BitVec.toNat_ofInt]; simp; omega
      rw [this]
    · exact Or.inl rfl

/-- Bucket records with the same bucket cache and a larger node cache: each node's tokens below. -/
theorem nodeTokL_nm_sub (v : View) (B B' : BRec) (r : NRec) (hbm : B'.bm = B.bm)
    (hnm : ∀ c, B'.nm !! c = none → B.nm !! c = none) :
    (nodeTokL v B' r).Subperm (nodeTokL v B r) := by
  have hop : opened B' = opened B := by unfold opened; rw [hbm]
  unfold nodeTokL
  refine (List.subperm_append_left _).2 (flatMap_subperm _ _ _ fun w _ => ?_)
  split
  · unfold entTokL; rw [hop]
  · unfold brTokL; rw [hop]
    split
    · rename_i h; rw [if_pos (hnm _ h)]
    · exact List.nil_subperm

theorem perm_shuffle (T own A C : List Nat) :
    (T ++ (own ++ (A ++ C))).Perm (own ++ (A ++ T ++ C)) :=
  List.perm_iff_count.2 fun a => by simp only [List.count_append]; omega

/-- The page a materialization reads from a file bucket has the position's id (`treeWF`; as
`Write.nodeAdded_pgid`, from the bucket's `bktClean`). -/
theorem nodeAdded_pgid_c (X : WX) (bl : Loc) (B : BRec) (pgid : w64) (parent : Loc)
    (pa : Loc) (pg : List w8) (hB : X.t.bs !! bl = some B)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (hpos : matPos X bl pgid parent)
    (hpg : wpageAt X.v B pgid = some (pa, pg)) (hin : B.ib.root' ≠ W64 0) :
    (pageHdr pg).id' = pgid := by
  have hpg' : X.v.pages !! pgid.toNat = some pg := by
    unfold wpageAt at hpg; rw [if_neg hin] at hpg
    cases h : X.v.pages !! pgid.toNat with
    | none => rw [h] at hpg; cases hpg
    | some pg' => rw [h] at hpg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpg
                  rw [hpg.2]
  have htw : treeWF X.v.pages X.t.mv.pgid'.toNat pgid.toNat := by
    obtain ⟨B1, hB1, hp⟩ := hpos
    rw [hB] at hB1; cases hB1
    rcases hp with ⟨-, hrn, rfl⟩ | ⟨i, r, w, hr, hleaf, hw, hwp, hnm⟩
    · exact (hc.2.1 hin).2 hrn
    · have hn := hc.2.2.2.2.2.2.2.1 parent r hr
      have hb := hn.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      have := (hb.2.2 w (List.mem_of_getElem? hw)).2.2
      rw [hwp] at this; exact this hnm
  cases htw with
  | page _ pg0 _ _ hpg0 hid _ _ =>
    rw [hpg'] at hpg0; cases hpg0
    apply BitVec.eq_of_toNat_eq; exact hid

/-- **One materialization keeps the tokens** (a sub-multiset; the view unchanged). -/
theorem txTokL_nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hbl : bktLocalOK X bl) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent) :
    (txTokL X').Subperm (txTokL X) ∧ X'.v = X.v := by
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h
  subst hX'
  refine ⟨?_, rfl⟩
  obtain ⟨-, B1, hB1, hc, -, -, -, hvw⟩ := hbl
  rw [hB] at hB1; cases hB1
  have hu := viewWF_unique X.v hvw
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hfresh : B.ns !! l = none := Write.objs_none X.t l hlo' bl B hB
  have hrws' : r.ws.map wDat = (pageWs pg).map wDat := by rw [hrws, Write.pageWsAs_wDat]
  -- the page of a file position
  have hpgv : B.ib.root' ≠ W64 0 → X.v.pages !! pgid.toNat = some pg := by
    intro hin
    unfold wpageAt at hpg; rw [if_neg hin] at hpg
    cases e : X.v.pages !! pgid.toNat with
    | none => rw [e] at hpg; cases hpg
    | some pg' =>
      rw [e] at hpg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpg
      rw [hpg.2]
  have hown : B.ib.root' ≠ W64 0 → r.nv.pgid'.toNat = pgid.toNat := by
    intro hin
    rw [hrid, nodeAdded_pgid_c X bl B pgid parent pa pg hB hc hpos hpg hin]
  let B' : BRec := { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }
  show (bktsTokL X.v (X.t.bs.insert bl B')).Subperm (bktsTokL X.v X.t.bs)
  refine flatMap_insert_subperm X.t.bs bl B B' _ _ hB ?_ fun _ _ _ _ => List.Subperm.refl _
  show (bktTokL X.v B').Subperm (bktTokL X.v B)
  obtain ⟨B0, hB0, hp⟩ := hpos
  rw [hB] at hB0; cases hB0
  rcases hcase with ⟨rfl, hbv, rfl⟩ | ⟨hpar, hbv, rp, rp', hrp0, hrpl, hrpcs, hrpws, hrpins, hrpkey,
    hrpks, hrpco, hrpnv, rfl⟩
  · -- the bucket's root page
    obtain ⟨-, hrn, rfl⟩ : (null : Loc) = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root' := by
      rcases hp with h | ⟨i, rp, w, hrp, -⟩
      · exact h
      · exfalso
        have hn := hc.2.2.2.2.2.2.2.1 null rp hrp
        exact (hc.2.2.2.2.1 _ _ hn.2.2.2.2.2.2.2.1).1 rfl
    have hns : B.ns = ∅ := (hc.2.2.1 hrn).1
    have hB'rn : B'.bv.rootNode' ≠ null := by
      show bv'.rootNode' ≠ null; rw [hbv]; exact hl0
    have hlist : bktTokL X.v B' = (FiniteMap.toList (B.ns.insert l r)).flatMap
        (fun p => nodeTokL X.v B' p.2) := by
      unfold bktTokL; rw [if_neg hB'rn]
    rw [hlist]
    refine ((flatMap_perm _ (toList_insert_perm B.ns l r)).subperm).trans ?_
    have hnil : FiniteMap.toList (GMap.delete l B.ns) = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun ⟨k, w⟩ hx => by
        have := (GMap.mem_toList _ _ _).1 hx
        by_cases e : k = l
        · subst e; rw [GMap.lookup_delete] at this; cases this
        · rw [GMap.lookup_delete_ne _ (Ne.symm e), hns] at this; simp at this
    rw [hnil]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold bktTokL
    rw [if_pos hrn]
    by_cases hin : B.ib.root' = W64 0
    · -- inline: the new node owns nothing
      rw [if_pos hin]
      have hipg : pg = B.ipg := by
        unfold wpageAt at hpg
        simp only [hin, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpg; exact hpg.2.symm
      subst hipg
      have hig := (hc.1 hin hrn).2.2.1
      have hid : r.nv.pgid' = W64 0 := by
        rw [hrid]; apply BitVec.eq_of_toNat_eq; have := hig.1; unfold pageId at this
        rw [this]; rfl
      have hleaf : r.nv.isLeaf' = true := by rw [hrleaf]; simp [hig.2.1]
      suffices nodeTokL X.v B' r = [] by rw [this]
      unfold nodeTokL ownTokL
      rw [if_pos hid, List.nil_append, entsTokL_wDat X.v B' _ r.ws (pageWs B.ipg) hrws', hleaf]
      unfold entsTokL pageWs
      rw [List.flatMap_map, List.flatMap_eq_nil_iff]
      intro i hi
      have hi := List.mem_range.1 hi
      simp only [↓reduceIte]
      unfold entTokL pageW
      simp only [hig.2.1, ↓reduceIte]
      rw [if_neg]
      rintro ⟨hb, -⟩
      have := shp_isBktFlag_mod _ hb
      have := (hig.2.2.2.2 i hi).2
      omega
    · rw [if_neg hin]
      have hpg' := hpgv hin
      have htw := (hc.2.1 hin).2 hrn
      exact newNode_sub X.v B B' pg r _ hu hpg' rfl hrws' hrleaf (hown hin) (treeWF_kind htw hpg')
  · -- a child of a branch node
    obtain ⟨i, rp0, w, hrp1, hleaf, hw, hwp, hnmp⟩ : ∃ i, pagePosAt B parent i pgid := by
      rcases hp with h | h
      · exact absurd h.1 hpar
      · exact h
    rw [hrp0] at hrp1; cases hrp1
    have hin : B.ib.root' ≠ W64 0 := fun h0 => by
      have := hc.2.2.2.2.2.2.1 h0 parent rp hrp0; rw [hleaf] at this; cases this
    have hrn : B.bv.rootNode' ≠ null := fun h0 => by
      rw [(hc.2.2.1 h0).1] at hrp0; cases hrp0
    have hB'rn : B'.bv.rootNode' ≠ null := by show bv'.rootNode' ≠ null; rw [hbv]; exact hrn
    have hlp : l ≠ parent := by intro e; rw [e, hrp0] at hfresh; cases hfresh
    unfold bktTokL
    rw [if_neg hB'rn, if_neg hrn]
    show ((FiniteMap.toList ((B.ns.insert parent rp').insert l r)).flatMap
      (fun p => nodeTokL X.v B' p.2)).Subperm _
    have hnm' : ∀ c, B'.nm !! c = none → B.nm !! c = none := by
      intro c hc'
      change (B.nm.insert pgid l) !! c = none at hc'
      by_cases e : pgid = c
      · subst e; rw [GMap.lookup_insert] at hc'; cases hc'
      · rwa [GMap.lookup_insert_ne _ _ e] at hc'
    refine flatMap_insert2_subperm B.ns l parent r rp rp' _ (fun p => nodeTokL X.v B p.2) hlp
      hfresh hrp0 ?_ fun k w _ _ => nodeTokL_nm_sub X.v B B' w rfl hnm'
    -- the parent's tokens: its entry `i` gives the new node its position's
    have hpgv' := hpgv hin
    have hn := hc.2.2.2.2.2.2.2.1 parent rp hrp0
    have htw : treeWF X.v.pages X.t.mv.pgid'.toNat pgid.toNat := by
      have hb := hn.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      have := (hb.2.2 w (List.mem_of_getElem? hw)).2.2
      rw [hwp] at this; exact this hnmp
    have hT := newNode_sub X.v B B' pg r _ hu hpgv' rfl hrws' hrleaf (hown hin)
      (treeWF_kind htw hpgv')
    dsimp only
    have hpgid : rp'.nv.pgid' = rp.nv.pgid' := by rw [hrpnv]
    have hlf' : rp'.nv.isLeaf' = rp.nv.isLeaf' := by rw [hrpnv]
    generalize nodeTokL X.v B' r = T at hT ⊢
    have hown' : ownTokL X.v rp' = ownTokL X.v rp := by unfold ownTokL; rw [hpgid]
    unfold nodeTokL
    rw [hown', hlf', hrpws, hleaf]
    obtain ⟨hi, hwi⟩ := List.getElem?_eq_some_iff.1 hw
    have hsplit : rp.ws = rp.ws.take i ++ w :: rp.ws.drop (i + 1) := by
      conv => lhs; rw [← List.take_append_drop i rp.ws]
      rw [List.drop_eq_getElem_cons hi, hwi]
    unfold entsTokL
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, Bool.false_eq_true, ↓reduceIte]
    have hw' : brTokL X.v B' w = [] := by
      unfold brTokL; rw [if_neg]; show (B.nm.insert pgid l) !! w.pgid ≠ none
      rw [hwp, GMap.lookup_insert]; simp
    have hw0 : brTokL X.v B w = pgIds (xPages X.v.pages (opened B) pgid.toNat) := by
      unfold brTokL; rw [if_pos (by rw [hwp]; exact hnmp), hwp]
    rw [hw', hw0, List.nil_append]
    refine (perm_shuffle _ _ _ _).subperm.trans ?_
    have hsub : ∀ ws : List WEntry, (ws.flatMap fun w => brTokL X.v B' w).Subperm
        (ws.flatMap fun w => brTokL X.v B w) := fun ws => by
      have := fun w => nodeTokL_nm_sub X.v B B' w rfl hnm'
      refine flatMap_subperm _ _ _ fun x _ => ?_
      unfold brTokL
      split
      · rename_i h; rw [if_pos (hnm' _ h)]
        have : opened B' = opened B := rfl
        rw [this]
      · exact List.nil_subperm
    refine (List.subperm_append_left _).2 ?_
    rw [← List.append_assoc]
    exact subperm_append' (subperm_append' (hsub _) hT) (hsub _)

/-- **Materializations keep the tokens** (`Cursor.node`'s `matGrow`; the bucket searchable at the
start, `bktLocalOK`, as `Cursor.node`'s pre). -/
theorem txTokL_matGrow (X X' : WX) (bl : Loc) (hbl : bktLocalOK X bl) (h : matGrow X X' bl) :
    (txTokL X').Subperm (txTokL X) ∧ X'.v = X.v := by
  induction h with
  | refl => exact ⟨List.Subperm.refl _, rfl⟩
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    have h1 := txTokL_nodeAdded X Y bl l pgid parent hbl hadd hpos
    have hbl' : bktLocalOK Y bl := by
      have hv : viewWF X.v := hbl.2.choose_spec.2.2.2.2.2
      refine Write.bktLocalOK_nodeAdded X Y bl l pgid parent hv hbl hadd hpos ?_ ?_
      · obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          hrvs, hcase, hX'⟩ := hadd
        intro B' r' hb' hr'
        have hB' : Y.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
          rw [hX']; exact GMap.lookup_insert _ _ _
        rw [hB'] at hb'; cases hb'
        have hns'l : ns' !! l = some r := by
          rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
            exact GMap.lookup_insert _ _ _
        have e : ns' !! l = some r' := hr'
        rw [hns'l] at e; cases e
        exact hrvs
      · obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          hrvs, hcase, hX'⟩ := hadd
        have hlo' : X.t.objs !! l = none := by simpa using hlo
        have hfresh : B.ns !! l = none := Write.objs_none X.t l hlo' bl B hB
        have hB' : Y.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
          rw [hX']; exact GMap.lookup_insert _ _ _
        intro B0 B1 rp0 rp1 hb0 hb1 hrp0 hrp1
        rw [hB] at hb0; cases hb0
        rw [hB'] at hb1; cases hb1
        have hpl : parent ≠ l := by intro e; rw [e, hfresh] at hrp0; cases hrp0
        rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, -, -, -, -, hco, -, rfl⟩
        · have e : (B.ns.insert l r) !! parent = some rp1 := hrp1
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), hrp0] at e
          cases e; rfl
        · have e : ((B.ns.insert parent rp').insert l r) !! parent = some rp1 := hrp1
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), GMap.lookup_insert] at e
          cases e
          rw [hrp0] at hrp; cases hrp
          exact hco
    have h2 := ih hbl'
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

end mat

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **`txShape` across materializations** (`bktLocalOK X bl`: `Cursor.node`'s pre; U7:
`Cursor.node`'s post in `Put`, `Delete`,
`CreateBucket(IfNotExists)`, `DeleteBucket`; U6: `Bucket_w`'s search). -/
theorem txShape_matGrow (γ : GName) (X X' : WX) (bl : Loc) (extra : GMap Nat Unit)
    (hbl : bktLocalOK X bl) (h : matGrow X X' bl) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  have ⟨hs, hv⟩ := txTokL_matGrow X X' bl hbl h
  exact txShape_sub γ X X' extra (by rw [hv]) fun _ => hs

end res

end bbolt
end EtcdGrove
end Perennial
