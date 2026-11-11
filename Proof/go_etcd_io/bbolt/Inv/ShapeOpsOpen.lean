/-
**A bucket's open keeps the writer's page tokens** (batch 37 item 14; `Inv/ShapeOps`):
`bktOpened` moves the opened nested bucket's tree from its parent (the leaf entry that stored it,
or the page position whose subtree holds it, which now excludes it: `opened`) to the new bucket
record. The opened bucket's pages are not reachable from the position but through its entry
(`xHas_not_opened`, from the view's uniqueness), so the parent's remaining tokens and the new
bucket's are disjoint. For U6's `Bucket.Bucket_w` (its post: `bktOpened X X' bl c nb g` and
`wOK X → wOK X'`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsMat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.Std go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section view
variable [GooseExts]

open Classical

/-- A page below `p` through its own page: below every ancestor of `p`. -/
theorem ownHas_extend {P : Pages} {a p x : Nat} {pg : List w8} (h : ownHas P a p)
    (hpg : P !! p = some pg) (hx : pageHas P pg x) : treeHas P a x := by
  induction h with
  | root root pg0 hpg0 => rw [hpg] at hpg0; cases hpg0; exact treeHas.sub root pg x hpg hx
  | child root pga k id hpga hfl hk _ ih =>
    exact treeHas.sub root pga x hpga (pageHas.child pga k x hfl hk (ih hpg))

/-- `xHas` from an ancestor through branches. -/
theorem ownHas_xHas {P : Pages} {op : List w8 → Prop} {a p x : Nat} (h : ownHas P a p)
    (hx : xHas P op p x) : xHas P op a x := by
  induction h with
  | root => exact hx
  | child root pga k id hpga hfl hk _ ih => exact xHas.child root pga k x hpga hfl hk (ih hx)

theorem ownHas_page {P : Pages} {a p : Nat} (h : ownHas P a p) : ∃ pga, P !! a = some pga := by
  cases h with
  | root _ pg hpg => exact ⟨pg, hpg⟩
  | child _ pga _ _ hpga => exact ⟨pga, hpga⟩

/-- **A nested bucket's pages are reached only through its entry** (`viewUnique`): from an
ancestor `a` of its leaf page `p` (through branches), excluding the bucket's key, no page of its
tree is reached. -/
theorem xHas_not_opened {P : Pages} (hu : viewUnique P) {op : List w8 → Prop} {p : Nat}
    {pg : List w8} {i : Nat} (hpg : P !! p = some pg) (hfl : pageFlags pg = leafPageFlag)
    (hi : i < pageCount pg) (hb : leafFlags pg i % 2 = bucketLeafFlag) (hop : op (leafKey pg i))
    {a x : Nat} (hx : xHas P op a x) (ha : ownHas P a p) (hbx : bucketHas P (leafValue pg i) x) :
    False := by
  have hlb : leafPageFlag ≠ branchPageFlag := by unfold leafPageFlag branchPageFlag; decide
  induction hx with
  | root root pga hpga =>
    -- `a = x`: a cycle through the bucket
    cases ha with
    | root _ pg0 hpg0 =>
      exact (hu.2 _ pg hpg hfl).2 i hi hb hbx
    | child _ pgb k _ hpgb hflb hk hown =>
      have e : pgb = pga := by rw [hpga] at hpgb; exact (Option.some.inj hpgb).symm
      rw [e] at hflb hk hown
      have := ownHas_extend hown hpg (pageHas.bucket pg i root hfl hi hb hbx)
      exact (hu.1 root pga hpga hflb).2 k hk this
  | child root pgr j id hpgr hflr hj hxc ih =>
    cases ha with
    | root _ pg0 hpg0 =>
      have e : pgr = pg := by rw [hpg] at hpgr; exact (Option.some.inj hpgr).symm
      rw [e, hfl] at hflr; exact hlb hflr
    | child _ pgb k _ hpgb hflb hk hown =>
      have e : pgb = pgr := by rw [hpgr] at hpgb; exact (Option.some.inj hpgb).symm
      rw [e] at hflb hk hown
      by_cases e : j = k
      · subst e; exact ih hown hbx
      · have h1 := xHas_treeHas hxc
        have h2 := ownHas_extend hown hpg (pageHas.bucket pg i id hfl hi hb hbx)
        exact (hu.1 root pgr hpgr hflb).1 j k hj hk e id h1 h2
  | bucket root pgr m id hpgr hflr hm hbm hno hbh =>
    cases ha with
    | root _ pg0 hpg0 =>
      have e : pgr = pg := by rw [hpg] at hpgr; exact (Option.some.inj hpgr).symm
      rw [e] at hflr hm hbm hno hbh
      have hne : m ≠ i := by rintro rfl; exact hno hop
      exact (hu.2 _ pg hpg hfl).1 m i hm hi hne hbm hb id hbh hbx
    | child _ pgb _ _ hpgb hflb =>
      have e : pgb = pgr := by rw [hpgr] at hpgb; exact (Option.some.inj hpgb).symm
      rw [e, hflr] at hflb; exact hlb hflb

/-- The tokens of a bucket opened on the tree `R`: its pages (`xPages` excluding nothing is the
tree). -/
theorem xPages_none_sub (P : Pages) (R : Nat) :
    (pgIds (xPages P (fun _ => False) R)).Subperm (pgIds (treePages P R)) :=
  List.subperm_of_subset (pgIds_nodup _) fun x hx => by
    rw [mem_xPages] at hx; rw [mem_treePages]; exact xHas_treeHas hx

/-- **A position's tokens when a nested bucket under it is opened**: the opened bucket's tree and
the position's remaining pages (excluding it too) are below the position's. -/
theorem xPages_open_sub (P : Pages) (hu : viewUnique P) (op : List w8 → Prop) (c0 p : Nat)
    (pg : List w8) (i : Nat) (hown : ownHas P c0 p) (hpg : P !! p = some pg)
    (hfl : pageFlags pg = leafPageFlag) (hi : i < pageCount pg)
    (hb : leafFlags pg i % 2 = bucketLeafFlag) (hno : ¬ op (leafKey pg i))
    (hR : inBucketRoot (leafValue pg i) ≠ 0) :
    (pgIds (xPages P (fun _ => False) (inBucketRoot (leafValue pg i))) ++
      pgIds (xPages P (fun k => op k ∨ k = leafKey pg i) c0)).Subperm (pgIds (xPages P op c0)) := by
  refine List.subperm_of_subset ?_ fun x hx => ?_
  · rw [List.nodup_append]
    refine ⟨pgIds_nodup _, pgIds_nodup _, fun a ha b hb' => ?_⟩
    rw [mem_xPages] at ha hb'
    rintro rfl
    exact xHas_not_opened hu (op := fun k => op k ∨ k = leafKey pg i) hpg hfl hi hb (Or.inr rfl)
      hb' hown (bucketHas.file _ _ hR (xHas_treeHas ha))
  · rw [mem_xPages]
    rcases List.mem_append.1 hx with hx | hx
    · rw [mem_xPages] at hx
      exact ownHas_xHas hown (xHas.bucket p pg i x hpg hfl hi hb hno
        (bucketHas.file _ _ hR (xHas_treeHas hx)))
    · rw [mem_xPages] at hx
      exact xHas_mono (fun k h => Or.inl h) hx

end view

section open_
variable [GooseExts]

open Classical

/-- The bucket record with `name` opened at `c`. -/
abbrev bOpen (B : BRec) (name : List w8) (c : Loc) : BRec := { B with bm := B.bm.insert name c }

theorem opened_bOpen (B : BRec) (name : List w8) (c : Loc) (k : List w8) :
    opened (bOpen B name c) k ↔ opened B k ∨ k = name := by
  unfold opened bOpen
  by_cases e : name = k
  · subst e; simp
  · rw [GMap.lookup_insert_ne _ _ e]; simp [Ne.symm e]

theorem opened_bOpen_eq (B : BRec) (name : List w8) (c : Loc) :
    opened (bOpen B name c) = fun k => opened B k ∨ k = name :=
  funext fun k => propext (opened_bOpen B name c k)

/-- Opening more buckets: each entry's tokens below. -/
theorem entTok_open_sub (v : View) (B : BRec) (name : List w8) (c : Loc) (leaf : Bool)
    (w : WEntry) :
    (if leaf = true then entTokL v (bOpen B name c) w else brTokL v (bOpen B name c) w).Subperm
      (if leaf = true then entTokL v B w else brTokL v B w) := by
  split
  · unfold entTokL
    split
    · rename_i h
      rw [if_pos ⟨h.1, h.2.1, fun ho => h.2.2 ((opened_bOpen B name c _).2 (Or.inl ho))⟩]
    · exact List.nil_subperm
  · unfold brTokL
    show (if B.nm !! w.pgid = none then _ else []).Subperm (if B.nm !! w.pgid = none then _ else [])
    split
    · rw [opened_bOpen_eq]
      exact pgIds_filter_subperm _ _ _ fun id _ _ h =>
        decide_eq_true (xHas_mono (fun k hk => Or.inl hk) (of_decide_eq_true h))
    · exact List.Subperm.refl _

theorem nodeTokL_open_sub (v : View) (B : BRec) (name : List w8) (c : Loc) (r : NRec) :
    (nodeTokL v (bOpen B name c) r).Subperm (nodeTokL v B r) :=
  (List.subperm_append_left _).2 (flatMap_subperm _ _ _ fun w _ => entTok_open_sub v B name c _ w)

/-- A list split at an entry: its contribution in front. -/
theorem flatMap_split_perm {α β : Type _} (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x)
    (f : α → List β) :
    (l.flatMap f).Perm (f x ++ ((l.take i).flatMap f ++ (l.drop (i + 1)).flatMap f)) := by
  obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.1 hx
  have hsplit : l = l.take i ++ x :: l.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons hi, hxi]
  conv => lhs; rw [hsplit]
  rw [List.flatMap_append, List.flatMap_cons]
  exact List.perm_iff_count.2 fun a => by simp only [List.count_append]; omega

/-- **A node's entry `j` absorbs the opened bucket's tokens** (`C`): its other entries' below. -/
theorem nodeTokL_open_at (v : View) (B : BRec) (name : List w8) (c : Loc) (r : NRec) (j : Nat)
    (w : WEntry) (hw : r.ws[j]? = some w) (Cl : List Nat)
    (hC : (Cl ++ (if r.nv.isLeaf' = true then entTokL v (bOpen B name c) w
      else brTokL v (bOpen B name c) w)).Subperm
      (if r.nv.isLeaf' = true then entTokL v B w else brTokL v B w)) :
    (Cl ++ nodeTokL v (bOpen B name c) r).Subperm (nodeTokL v B r) := by
  unfold nodeTokL entsTokL
  generalize hF' : (fun w => if r.nv.isLeaf' = true then entTokL v (bOpen B name c) w
    else brTokL v (bOpen B name c) w) = F' at hC ⊢
  generalize hF : (fun w => if r.nv.isLeaf' = true then entTokL v B w
    else brTokL v B w) = F at hC ⊢
  have hle : ∀ x, (F' x).Subperm (F x) := fun x => by
    rw [← hF, ← hF']; exact entTok_open_sub v B name c _ x
  have hC : (Cl ++ F' w).Subperm (F w) := by rw [← hF, ← hF']; exact hC
  have p1 := flatMap_split_perm r.ws j w hw F'
  have p2 := flatMap_split_perm r.ws j w hw F
  have key : (Cl ++ F' w ++ ((r.ws.take j).flatMap F' ++ (r.ws.drop (j + 1)).flatMap F')).Subperm
      (F w ++ ((r.ws.take j).flatMap F ++ (r.ws.drop (j + 1)).flatMap F)) :=
    subperm_append' hC (subperm_append' (flatMap_subperm _ _ _ fun x _ => hle x)
      (flatMap_subperm _ _ _ fun x _ => hle x))
  have q1 : (Cl ++ (ownTokL v r ++ r.ws.flatMap F')).Perm (ownTokL v r ++
      (Cl ++ F' w ++ ((r.ws.take j).flatMap F' ++ (r.ws.drop (j + 1)).flatMap F'))) :=
    List.perm_iff_count.2 fun a => by
      have := p1.count_eq a; simp only [List.count_append] at this ⊢; omega
  have q2 : (ownTokL v r ++ (F w ++ ((r.ws.take j).flatMap F ++
      (r.ws.drop (j + 1)).flatMap F))).Perm (ownTokL v r ++ r.ws.flatMap F) :=
    List.perm_iff_count.2 fun a => by
      have := p2.count_eq a; simp only [List.count_append] at this ⊢; omega
  exact q1.subperm.trans (((List.subperm_append_left _).2 key).trans q2.subperm)

/-- A bucket with more buckets opened: its tokens below. -/
theorem bktTokL_open_sub (v : View) (B : BRec) (name : List w8) (c : Loc) :
    (bktTokL v (bOpen B name c)).Subperm (bktTokL v B) := by
  unfold bktTokL
  show (if B.bv.rootNode' = null then (if B.ib.root' = W64 0 then [] else _) else _).Subperm
    (if B.bv.rootNode' = null then (if B.ib.root' = W64 0 then [] else _) else _)
  split
  · split
    · exact List.Subperm.refl _
    · rw [opened_bOpen_eq]
      exact pgIds_filter_subperm _ _ _ fun id _ _ h =>
        decide_eq_true (xHas_mono (fun k hk => Or.inl hk) (of_decide_eq_true h))
  · exact flatMap_subperm _ _ _ fun p _ => nodeTokL_open_sub v B name c p.2

/-- One binding absorbs the extra tokens `Cl`; every binding's tokens below. -/
theorem flatMap_absorb {K V : Type _} [DecidableEq K] (m : GMap K V) (k : K) (x : V)
    (hk : m !! k = some x) (Cl : List Nat) (f g : K × V → List Nat)
    (hx : (Cl ++ f (k, x)).Subperm (g (k, x))) (hy : ∀ y, (f y).Subperm (g y)) :
    (Cl ++ (FiniteMap.toList m).flatMap f).Subperm ((FiniteMap.toList m).flatMap g) := by
  have p1 := flatMap_perm f (toList_lookup_perm m k x hk)
  have p2 := flatMap_perm g (toList_lookup_perm m k x hk)
  simp only [List.flatMap_cons] at p1 p2
  refine List.Subperm.trans ?_ p2.symm.subperm
  refine ((p1.append_left Cl).subperm).trans ?_
  rw [← List.append_assoc]
  exact subperm_append' hx (flatMap_subperm _ _ _ fun y _ => hy y)

/-- **A bucket's open keeps the tokens** (a sub-multiset; the view unchanged): the opened bucket's
tree moves from its parent's position or leaf entry to the new record. `wOK X'` (`Bucket_w`'s
post) gives where the entry is (`bktNested`'s `entryIn`) and the view's uniqueness. -/
theorem txTokL_bktOpened (X X' : WX) (bl c : Loc) (name : List w8) (g : Nat) (hok' : wOK X')
    (h : bktOpened X X' bl c name g) : (txTokL X').Subperm (txTokL X) ∧ X'.v = X.v := by
  obtain ⟨B, C, w, hB, -, -, -, hbm, -, hcfresh, -, -, hCrn, -, hCbm, -, -, -, hX'⟩ := h
  have hv : X'.v = X.v := by rw [hX']
  have hbs' : X'.t.bs = (X.t.bs.insert bl (bOpen B name c)).insert c C := by rw [hX']
  refine ⟨?_, hv⟩
  have hu := viewWF_unique X'.v hok'.2.2.2.2.2.2.2
  rw [hv] at hu
  have hbsc : X.t.bs !! c = none := by
    have := hcfresh; unfold WTx.bobjs at this; rw [GMap.lookup_union] at this
    cases e : X.t.bs !! c with
    | none => rfl
    | some _ => rw [e] at this; simp at this
  have hcb : c ≠ bl := by intro e; rw [e, hB] at hbsc; cases hbsc
  unfold txTokL; rw [hv, hbs']
  refine flatMap_insert2_subperm X.t.bs c bl C B (bOpen B name c) _ (fun p => bktTokL X.v p.2) hcb
    hbsc hB ?_ fun _ _ _ _ => List.Subperm.refl _
  show (bktTokL X.v C ++ bktTokL X.v (bOpen B name c)).Subperm (bktTokL X.v B)
  -- the records after the open
  have hB' : X'.t.bs !! bl = some (bOpen B name c) := by
    rw [hbs', GMap.lookup_insert_ne _ _ hcb, GMap.lookup_insert]
  have hC' : X'.t.bs !! c = some C := by rw [hbs']; exact GMap.lookup_insert _ _ _
  obtain ⟨C1, v, hC1, hin, -, -, hroot, -⟩ :=
    (hok'.2.1 bl (bOpen B name c) hB').2 name c (GMap.lookup_insert _ _ _)
  rw [hv] at hin
  rw [hC'] at hC1; cases hC1
  have hcl := (hok'.1.2.2.2.2.2 bl (bOpen B name c) hB').1
  have hopC : opened C = fun _ => False := by
    funext k; apply propext; unfold opened; rw [hCbm]; simp
  have hnoB : ¬ opened B name := by unfold opened; rw [hbm]; simp
  -- the opened bucket's tokens
  by_cases hR0 : C.ib.root' = W64 0
  · have : bktTokL X.v C = [] := by unfold bktTokL; rw [if_pos hCrn, if_pos hR0]
    rw [this, List.nil_append]; exact bktTokL_open_sub X.v B name c
  have hR : inBucketRoot v ≠ 0 := by
    intro e; apply hR0; apply BitVec.eq_of_toNat_eq; rw [hroot]; exact e
  have hCl : bktTokL X.v C = pgIds (xPages X.v.pages (fun _ => False) (inBucketRoot v)) := by
    unfold bktTokL; rw [if_pos hCrn, if_neg hR0, hopC, hroot]; rfl
  rw [hCl]
  have hns : (bOpen B name c).ns = B.ns := rfl
  have hbv : (bOpen B name c).bv = B.bv := rfl
  have hib : (bOpen B name c).ib = B.ib := rfl
  -- the tokens of a bucket with a root node
  have hnode : B.bv.rootNode' ≠ null → bktTokL X.v (bOpen B name c) =
      (FiniteMap.toList B.ns).flatMap (fun p => nodeTokL X.v (bOpen B name c) p.2) ∧
      bktTokL X.v B = (FiniteMap.toList B.ns).flatMap (fun p => nodeTokL X.v B p.2) := by
    intro hrn
    unfold bktTokL; rw [hbv, hns, if_neg hrn, if_neg hrn]; exact ⟨rfl, rfl⟩
  rcases hin with ⟨l, r, w', hr, hlf, hw', hk, hf, hval⟩ |
    ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, hk, hf, hval⟩
  · -- a materialized leaf's entry
    rw [hns] at hr
    have hrn : B.bv.rootNode' ≠ null := fun h0 => by
      have := (hcl.2.2.1 h0).1; rw [hns] at this; rw [this] at hr; simp at hr
    rw [(hnode hrn).1, (hnode hrn).2]
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hw'
    refine flatMap_absorb B.ns l r hr _ _ _ ?_ (fun y => nodeTokL_open_sub X.v B name c y.2)
    refine nodeTokL_open_at X.v B name c r j w' hj _ ?_
    simp only [hlf, ↓reduceIte]
    have e1 : entTokL X.v (bOpen B name c) w' = [] := by
      unfold entTokL; rw [if_neg]; intro h; exact h.2.2 ((opened_bOpen B name c _).2 (Or.inr hk))
    have e2 : entTokL X.v B w' = pgIds (treePages X.v.pages (inBucketRoot v)) := by
      unfold entTokL
      rw [if_pos ⟨hf, by rw [hval]; exact hR, by rw [hk]; exact hnoB⟩, hval]
    rw [e1, e2, List.append_nil]
    exact xPages_none_sub X.v.pages (inBucketRoot v)
  · -- an entry of a page under a position
    have key := xPages_open_sub X.v.pages hu (opened B) c0 p pg i hown hpg hfl hi hf
      (by rw [hk]; exact hnoB) (by rw [hval]; exact hR)
    rw [hk, hval] at key
    rcases hpr with ⟨hrn, hr0, rfl⟩ | ⟨l, j, ⟨r, w', hr, hlf, hj, hwp, hnm⟩, hc0⟩
    · rw [hbv] at hrn; rw [hib] at hr0
      unfold bktTokL; rw [hbv, hib, if_pos hrn, if_pos hrn, if_neg hr0, if_neg hr0, opened_bOpen_eq]
      exact key
    · rw [hns] at hr
      have hrn : B.bv.rootNode' ≠ null := fun h0 => by
        have := (hcl.2.2.1 h0).1; rw [hns] at this; rw [this] at hr; simp at hr
      rw [(hnode hrn).1, (hnode hrn).2]
      refine flatMap_absorb B.ns l r hr _ _ _ ?_ (fun y => nodeTokL_open_sub X.v B name c y.2)
      refine nodeTokL_open_at X.v B name c r j w' hj _ ?_
      simp only [hlf, Bool.false_eq_true, ↓reduceIte]
      have hc : w'.pgid.toNat = c0 := by
        rw [hwp]; rw [BitVec.toNat_ofInt]; simp; omega
      have hnm' : B.nm !! w'.pgid = none := by rw [hwp]; exact hnm
      unfold brTokL
      rw [show (bOpen B name c).nm = B.nm from rfl, if_pos hnm', if_pos hnm', opened_bOpen_eq, hc]
      exact key

end open_

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **`txShape` across a bucket's open** (U6: `Bucket.Bucket_w`'s uncached case, with its post's
`wOK X → wOK X'`). -/
theorem txShape_bktOpened (γ : GName) (X X' : WX) (bl c : Loc) (name : List w8) (g : Nat)
    (extra : GMap Nat Unit) (hok' : wOK X') (h : bktOpened X X' bl c name g) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  have ⟨hs, hv⟩ := txTokL_bktOpened X X' bl c name g hok' h
  exact txShape_sub γ X X' extra (by rw [hv]) fun _ => hs

end res

end bbolt
end EtcdGrove
end Perennial
