/-
The writer's shape (`WriteTxShape.lean`) across `Bucket.node`: materializing a page position (a
child of a branch node, or the bucket's root page with no root node) keeps the bucket's shape.

**Tokens.** The position's tokens (`pgToks` of `xPages`, its tree but the opened nested buckets)
split into the new node's page's token and, a branch, its children's subtrees' tokens, or, a
leaf, its unopened nested buckets' trees' tokens; the parts are disjoint by the view's
`viewUnique`. Tokens are handled pointwise (`tokB`: over the view's pages, a token where a
predicate holds), so a split is a pointwise fact. The parent's entry for the position gives up
its tokens (its child is now materialized); every other node's tokens stay as they are.

**Keys.** The new node's bounds are its entry's (`entryBnd` of the parent's), or none for the
root; its keys are its page's, inside them by the tree's `treeKeys`; its children are not
materialized (`posNodeFree`), with the page's keys and bounds.

**Nested buckets.** An entry on a page of the position is now in the new leaf, or on a page of
one of the new node's children (a new position); the other positions stay.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.WriteTxClean

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem xHas_treeHas {pages : GMap Nat (List w8)} {op : List w8 → Prop} {c id : Nat}
    (h : xHas pages op c id) : treeHas pages c id := by
  induction h with
  | root root pg hpg => exact treeHas.root root pg hpg
  | child root pg i id hpg hb hi _ ih =>
    exact treeHas.sub root pg id hpg (pageHas.child pg i id hb hi ih)
  | bucket root pg i id hpg hl hi hf _ hb =>
    exact treeHas.sub root pg id hpg (pageHas.bucket pg i id hl hi hf hb)

theorem ownHas_cases {pages : GMap Nat (List w8)} {c p : Nat} (pg : List w8)
    (hpg : pages !! c = some pg) (h : ownHas pages c p) :
    p = c ∨ (pageFlags pg = branchPageFlag ∧ ∃ i < pageCount pg, ownHas pages (branchPgid pg i) p) := by
  cases h with
  | root _ _ _ => exact Or.inl rfl
  | child _ pg' i _ hpg' hb hi h =>
    rw [hpg] at hpg'; cases hpg'
    exact Or.inr ⟨hb, i, hi, h⟩

theorem leafFlags_lt (pg : List w8) (i : Nat) : leafFlags pg i < 2 ^ 32 := leAt_lt _ _ 4

theorem isBkt_pageW (pg : List w8) (src : Src) (i : Nat) (hl : pageFlags pg = leafPageFlag) :
    isBktFlag (pageW pg src i).flags ↔ leafFlags pg i % 2 = bucketLeafFlag := by
  unfold pageW; rw [if_pos hl]; exact isBktFlag_iff _ (leafFlags_lt pg i)

theorem pageW_leaf (pg : List w8) (src : Src) (i : Nat) (hl : pageFlags pg = leafPageFlag) :
    (pageW pg src i).key = leafKey pg i ∧ (pageW pg src i).value = leafValue pg i ∧
      (pageW pg src i).flags = W32 (leafFlags pg i) := by
  unfold pageW; rw [if_pos hl]; exact ⟨rfl, rfl, rfl⟩

theorem pageW_branch (pg : List w8) (src : Src) (i : Nat) (hl : pageFlags pg ≠ leafPageFlag) :
    (pageW pg src i).key = branchKey pg i ∧ (pageW pg src i).pgid = W64 (branchPgid pg i) := by
  unfold pageW; rw [if_neg hl]; exact ⟨rfl, rfl⟩

theorem pageW_key_pageKey (pg : List w8) (src : Src) (i : Nat) :
    (pageW pg src i).key = pageKey pg i := by
  unfold pageW pageKey; split <;> rfl

theorem branch_ne_leaf : branchPageFlag ≠ leafPageFlag := by
  unfold branchPageFlag leafPageFlag; decide

/-- The bounds of a node read from a branch page: its page's. -/
theorem entryBnd_pageWs (b : Option (List w8) × Option (List w8)) (pg : List w8) (src : Src)
    (i : Nat) (hi : i < pageCount pg) (hl : pageFlags pg ≠ leafPageFlag) :
    entryBnd b (pageWs pg src) i =
      (childLo b.1 (branchKey pg) i, childHi b.2 (branchKey pg) (pageCount pg) i) := by
  unfold entryBnd childLo childHi
  rw [pageWs_length]
  congr 1
  · split
    · rfl
    · rw [wKey_pageWs_i _ _ _ hi, (pageW_branch pg src i hl).1]
  · split
    · rename_i h
      rw [wKey_pageWs_i _ _ _ h, (pageW_branch pg src _ hl).1]
    · rfl

/-- The keys of a page are inside the bounds of its tree. -/
theorem treeKeys_pageWs (pages : GMap Nat (List w8)) (c : Nat) (lo hi : Option (List w8))
    (pg : List w8) (src : Src) (h : treeKeys pages c lo hi) (hpg : pages !! c = some pg) :
    ∀ w ∈ pageWs pg src, keyIn lo hi w.key := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := pageWs_mem pg src w hw
  cases h with
  | leaf _ pg' _ _ hpg' hl hk _ =>
    rw [hpg] at hpg'; cases hpg'
    rw [(pageW_leaf pg src i hl).1]; exact hk i hi
  | branch _ pg' _ _ _ hpg' hb _ hk _ _ =>
    rw [hpg] at hpg'; cases hpg'
    rw [(pageW_branch pg src i (by rw [hb]; exact branch_ne_leaf)).1]; exact hk i hi

theorem nodup_pgid_ne (ws : List WEntry) (h : (ws.map WEntry.pgid).Nodup) (i k : Nat)
    (w x : WEntry) (hi : ws[i]? = some w) (hk : ws[k]? = some x) (hne : k ≠ i) :
    x.pgid ≠ w.pgid := by
  intro he
  have hil := (List.getElem?_eq_some_iff.1 hi).1
  have hkl := (List.getElem?_eq_some_iff.1 hk).1
  have h1 : (ws.map WEntry.pgid)[k]? = some x.pgid := by rw [List.getElem?_map, hk]; rfl
  have h2 : (ws.map WEntry.pgid)[i]? = some w.pgid := by rw [List.getElem?_map, hi]; rfl
  rw [he] at h1
  exact hne ((List.Nodup.getElem?_inj (by simpa using hkl) h).1 (h1.trans h2.symm))

end pure

/-! ### Tokens, pointwise -/

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The tokens of the pages of `pages` where `p` holds. -/
def tokB (γ : GName) (pages : GMap Nat (List w8)) (p : Nat → Bool) : IProp GF :=
  [∗map] id ↦ _pg ∈ pages, if p id then id ↪[γ] () else emp

theorem pgToks_filter (γ : GName) (pages : GMap Nat (List w8)) (p : Nat → Bool) :
    pgToks (GF := GF) γ (GMap.filter (fun id _ => p id) pages) = tokB γ pages p := by
  have he : GMap.filter (fun id _ => p id) pages =
      Iris.Std.PartialMap.filter (fun id _ => p id) pages := by
    apply GMap.ext; intro k
    show (pages !! k).filter (fun _ => p k) = (pages !! k).bind fun v => if p k then some v else none
    cases pages !! k <;> simp [Option.filter]
  unfold pgToks tokB
  rw [he, BigSepM.bigSepM_filter_cond]

theorem tokB_mono (γ : GName) (pages : GMap Nat (List w8)) (p q : Nat → Bool)
    (h : ∀ id, q id = true → p id = true) : tokB (GF := GF) γ pages p ⊢ tokB γ pages q := by
  unfold tokB
  apply BigSepM.bigSepM_mono
  intro id _ _
  by_cases hq : q id = true
  · rw [if_pos hq, if_pos (h id hq)]
  · rw [if_neg hq]; split
    · exact Affine.affine
    · exact .rfl

theorem tokB_emp (γ : GName) (pages : GMap Nat (List w8)) : ⊢ tokB (GF := GF) γ pages (fun _ => false) := by
  unfold tokB
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact BigSepM.bigSepM_emp.2

theorem tok_pt_split (t : IProp GF) (id : Nat) (p : Nat → Bool) (Fs : List (Nat → Bool))
    (hsub : ∀ f ∈ Fs, f id = true → p id = true)
    (hdisj : Fs.Pairwise (fun f g => ¬ (f id = true ∧ g id = true))) :
    (if p id then t else emp) ⊢ [∗list] f ∈ Fs, if f id then t else emp := by
  induction Fs with
  | nil =>
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_nil.2
    split
    · exact Affine.affine
    · exact .rfl
  | cons f Fs ih =>
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2
    obtain ⟨hhd, htl⟩ := List.pairwise_cons.1 hdisj
    by_cases hf : f id = true
    · rw [if_pos (hsub f List.mem_cons_self hf), if_pos hf]
      refine sep_emp.2.trans (sep_mono_right ?_)
      refine BIBase.Entails.trans ?_ (BigSepL.bigSepL_mono (Φ := fun _ _ => (emp : IProp GF)) ?_)
      · exact BigSepL.bigSepL_emp.2
      · intro k g hg
        have := hhd g (List.mem_of_getElem? hg)
        rw [if_neg (fun h => this ⟨hf, h⟩)]
    · rw [if_neg hf]
      exact emp_sep.2.trans (sep_mono_right (ih (fun g hg => hsub g (List.mem_cons_of_mem _ hg)) htl))

/-- Splitting the tokens of `p` into disjoint parts. -/
theorem tokB_split (γ : GName) (pages : GMap Nat (List w8)) (p : Nat → Bool)
    (Fs : List (Nat → Bool)) (hsub : ∀ f ∈ Fs, ∀ id, f id = true → p id = true)
    (hdisj : Fs.Pairwise (fun f g => ∀ id, ¬ (f id = true ∧ g id = true))) :
    tokB (GF := GF) γ pages p ⊢ [∗list] f ∈ Fs, tokB γ pages f := by
  unfold tokB
  refine (BigSepM.bigSepM_mono fun {id _} _ => tok_pt_split (id ↪[γ] ()) id p Fs
    (fun f hf => hsub f hf id) (hdisj.imp fun h => h id)).trans ?_
  exact (BigSepM.bigSepM_comm_list (fun id _ _ f => if f id then id ↪[γ] () else emp) pages Fs).1

theorem pairwise_range_map {α : Type} (R : α → α → Prop) (n : Nat) (f : Nat → α)
    (h : ∀ i j, i < n → j < n → i ≠ j → R (f i) (f j)) :
    ((List.range n).map f).Pairwise R := by
  rw [List.pairwise_map]
  exact (List.nodup_range).imp_of_mem fun ha hb hne =>
    h _ _ (List.mem_range.1 ha) (List.mem_range.1 hb) hne

end toks

/-! ### Tokens of nodes -/

section nodetoks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem opened_eq (B B' : BRec) (h : B'.bm = B.bm) : opened B' = opened B := by
  funext k; unfold opened; rw [h]

open Classical in
/-- The tokens of the position `c` (page `pg`) are those of the node read from it. -/
theorem toks_newNode (γ : GName) (W : WView) (hv : viewOK W) (B' : BRec) (op : List w8 → Prop)
    (hop : opened B' = op) (c : Nat) (pg : List w8) (hpg : W.pages !! c = some pg)
    (hfl : pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) (r : NRec) (src : Src)
    (hws : r.ws = pageWs pg src) (hleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag))
    (hpid : r.nv.pgid' ≠ W64 0 → uint.nat r.nv.pgid' = c) :
    pgToks (GF := GF) γ (xPages W.pages op c) ⊢ nodeToks γ W B' r := by
  have huniq := hv.2.2.2.2.2
  unfold xPages
  rw [pgToks_filter γ W.pages (fun id => decide (xHas W.pages op c id))]
  have hown : tokB (GF := GF) γ W.pages (fun id => decide (id = c)) ⊢
      if r.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat r.nv.pgid')) W.pages) := by
    by_cases h0 : r.nv.pgid' = W64 0
    · rw [if_pos h0]; exact Affine.affine
    · rw [if_neg h0, pgToks_filter γ W.pages (fun id => decide (id = uint.nat r.nv.pgid'))]
      apply tokB_mono; intro id h
      simp only [decide_eq_true_iff] at h ⊢; rw [← hpid h0]; exact h
  rcases hfl with hl | hb
  · let Fs : List (Nat → Bool) := (fun id => decide (id = c)) :: (List.range (pageCount pg)).map
      (fun i id => decide (leafFlags pg i % 2 = bucketLeafFlag ∧ ¬ op (leafKey pg i) ∧
        inBucketRoot (leafValue pg i) ≠ 0 ∧ treeHas W.pages (inBucketRoot (leafValue pg i)) id))
    refine (tokB_split γ W.pages _ Fs ?_ ?_).trans ?_
    · intro f hf id hid
      simp only [decide_eq_true_iff]
      rcases List.mem_cons.1 hf with rfl | hf
      · simp only [decide_eq_true_iff] at hid; subst hid; exact xHas.root _ pg hpg
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        simp only [decide_eq_true_iff] at hid
        obtain ⟨h1, h2, h3, h4⟩ := hid
        exact xHas.bucket c pg i id hpg hl (List.mem_range.1 hi) h1 h2 (bucketHas.file _ id h3 h4)
    · refine List.pairwise_cons.2 ⟨?_, pairwise_range_map _ _ _ ?_⟩
      · intro g hg id ⟨h1, h2⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
        simp only [decide_eq_true_iff] at h1 h2
        subst h1
        exact (huniq.2 _ pg hpg hl).2 i (List.mem_range.1 hi) h2.1 (bucketHas.file _ _ h2.2.2.1 h2.2.2.2)
      · intro i j hi hj hij id ⟨h1, h2⟩
        simp only [decide_eq_true_iff] at h1 h2
        exact (huniq.2 _ pg hpg hl).1 i j hi hj hij h1.1 h2.1 id
          (bucketHas.file _ _ h1.2.2.1 h1.2.2.2) (bucketHas.file _ _ h2.2.2.1 h2.2.2.2)
    · refine BigSepL.bigSepL_cons.1.trans ?_
      unfold nodeToks
      refine sep_mono hown ?_
      rw [BigSepL.bigSepL_map, hws]
      unfold pageWs
      rw [BigSepL.bigSepL_map]
      apply BigSepL.bigSepL_mono
      intro k i hk
      have hi : i < pageCount pg := List.mem_range.1 (List.mem_of_getElem? hk)
      rw [hleaf]
      simp only [hl, _root_.decide_true, ↓reduceIte]
      obtain ⟨hk1, hv1, -⟩ := pageW_leaf pg src i hl
      split
      · rename_i h
        obtain ⟨h1, h2, h3⟩ := h
        unfold treePages
        rw [pgToks_filter γ W.pages (fun id => decide (treeHas W.pages (inBucketRoot (pageW pg src i).value) id))]
        apply tokB_mono
        intro id hid
        simp only [decide_eq_true_iff] at hid ⊢
        rw [hv1] at hid h2
        rw [hk1, hop] at h3
        exact ⟨(isBkt_pageW pg src i hl).1 h1, h3, h2, hid⟩
      · exact Affine.affine
  · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hb]; exact branch_ne_leaf
    let Fs : List (Nat → Bool) := (fun id => decide (id = c)) :: (List.range (pageCount pg)).map
      (fun i id => decide (xHas W.pages op (branchPgid pg i) id))
    refine (tokB_split γ W.pages _ Fs ?_ ?_).trans ?_
    · intro f hf id hid
      simp only [decide_eq_true_iff]
      rcases List.mem_cons.1 hf with rfl | hf
      · simp only [decide_eq_true_iff] at hid; subst hid; exact xHas.root _ pg hpg
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        simp only [decide_eq_true_iff] at hid
        exact xHas.child c pg i id hpg hb (List.mem_range.1 hi) hid
    · refine List.pairwise_cons.2 ⟨?_, pairwise_range_map _ _ _ ?_⟩
      · intro g hg id ⟨h1, h2⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
        simp only [decide_eq_true_iff] at h1 h2
        subst h1
        exact (huniq.1 _ pg hpg hb).2 i (List.mem_range.1 hi) (xHas_treeHas h2)
      · intro i j hi hj hij id ⟨h1, h2⟩
        simp only [decide_eq_true_iff] at h1 h2
        exact (huniq.1 _ pg hpg hb).1 i j hi hj hij id (xHas_treeHas h1) (xHas_treeHas h2)
    · refine BigSepL.bigSepL_cons.1.trans ?_
      unfold nodeToks
      refine sep_mono hown ?_
      rw [BigSepL.bigSepL_map, hws]
      unfold pageWs
      rw [BigSepL.bigSepL_map]
      apply BigSepL.bigSepL_mono
      intro k i hk
      rw [hleaf]
      simp only [hnl, decide_false, Bool.false_eq_true, ↓reduceIte]
      split
      · rw [(pageW_branch pg src i hnl).2, uint_nat_W64_w _ (branchPgid_lt pg i), hop]
        unfold xPages
        rw [pgToks_filter γ W.pages (fun id => decide (xHas W.pages op (branchPgid pg i) id))]
      · exact Affine.affine

/-- A node's tokens, in a bucket that changed none of its children's nodes. -/
theorem nodeToks_congr (γ : GName) (W : WView) (B B' : BRec) (r r' : NRec) (hbm : B'.bm = B.bm)
    (hp : r'.nv.pgid' = r.nv.pgid') (hws : r'.ws = r.ws) (hl : r'.nv.isLeaf' = r.nv.isLeaf')
    (hnm : r.nv.isLeaf' = false → ∀ w ∈ r.ws, B'.nm !! w.pgid = B.nm !! w.pgid) :
    nodeToks (GF := GF) γ W B r ⊢ nodeToks γ W B' r' := by
  unfold nodeToks
  rw [hp, hws, hl, opened_eq B B' hbm]
  refine sep_mono .rfl (BigSepL.bigSepL_mono fun {k w} hk => ?_)
  by_cases hlf : r.nv.isLeaf' = true
  · simp only [hlf, ↓reduceIte]; exact .rfl
  · have hf : r.nv.isLeaf' = false := by simpa using hlf
    rw [if_neg hlf, if_neg hlf, hnm hf w (List.mem_of_getElem? hk)]

/-- The parent of a materialized position gives up its tokens. -/
theorem nodeToks_parent (γ : GName) (W : WView) (B B' : BRec) (rp rp' : NRec) (hbm : B'.bm = B.bm)
    (hp : rp'.nv.pgid' = rp.nv.pgid') (hws : rp'.ws = rp.ws) (hl : rp'.nv.isLeaf' = rp.nv.isLeaf')
    (hbr : rp.nv.isLeaf' = false) (i : Nat) (w : WEntry) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (hsome : B'.nm !! w.pgid ≠ none)
    (hnd : (rp.ws.map WEntry.pgid).Nodup) (hnm : ∀ k, k ≠ w.pgid → B'.nm !! k = B.nm !! k) :
    nodeToks (GF := GF) γ W B rp ⊢
      pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid)) ∗ nodeToks γ W B' rp' := by
  unfold nodeToks
  rw [hp, hws, hl, opened_eq B B' hbm, hbr]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hlist : ([∗list] x ∈ rp.ws, if B.nm !! x.pgid = none then
        pgToks (GF := GF) γ (xPages W.pages (opened B) (uint.nat x.pgid)) else emp) ⊢
      pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid)) ∗
      [∗list] x ∈ rp.ws, if B'.nm !! x.pgid = none then
        pgToks γ (xPages W.pages (opened B) (uint.nat x.pgid)) else emp := by
    refine (BigSepL.bigSepL_mono (Ψ := fun k x =>
      iprop((if k = i then pgToks (GF := GF) γ (xPages W.pages (opened B) (uint.nat w.pgid)) else emp) ∗
        (if B'.nm !! x.pgid = none then
          pgToks γ (xPages W.pages (opened B) (uint.nat x.pgid)) else emp))) ?_).trans ?_
    · intro k x hk
      by_cases hki : k = i
      · subst hki
        rw [hw] at hk; cases hk
        rw [if_pos rfl, if_pos hnone, if_neg hsome]
        exact sep_emp.2
      · rw [if_neg hki, hnm _ (nodup_pgid_ne rp.ws hnd i k w x hw hk hki)]
        exact emp_sep.2
    · refine BigSepL.bigSepL_sep_eqv.1.trans (sep_mono ?_ .rfl)
      refine (BigSepL.bigSepL_lookup (Φ := fun k _ =>
        if k = i then pgToks (GF := GF) γ (xPages W.pages (opened B) (uint.nat w.pgid)) else emp) hw).trans ?_
      rw [if_pos rfl]
  iintro ⟨Ho, Hl⟩
  icases hlist $$ Hl with ⟨HX, Hl⟩
  iframe

end nodetoks

/-! ### The bucket's tokens -/

section bkttoks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- Materializing the page position `w.pgid` (entry `i` of the branch node `nl`) keeps the
bucket's tokens. -/
theorem bktToks_addChild (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat w.pgid = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src) :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') := by
  obtain ⟨-, -, hc3, -, -, -, -, hc8, hc9, -⟩ := hc
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc3 h0).1; rw [this] at hrp; cases hrp
  have hbv' : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by
    simp [nodeAdded, hnl]
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrp12, -⟩ := hc8 nl rp hrp
  obtain ⟨-, hnd, hkids⟩ := hrp12 hbr
  obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
  obtain ⟨-, hpid, -, hkind⟩ := treeWF_page _ _ _ pg (hcwf hnone) hpg
  have hpos : pagePosAt B nl i w.pgid := ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩
  have hcself := treeHas_self _ _ pg hpg
  have hnm' : ∀ k, (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! k =
      if k = w.pgid then some l else B.nm !! k := by
    intro k; show (<[w.pgid := l]> B.nm) !! k = _
    by_cases hk : k = w.pgid
    · subst hk; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]
  let rp' : NRec := { rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] }
  have hns_eq : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').ns =
      Iris.Std.PartialMap.insert (Iris.Std.PartialMap.insert (Iris.Std.PartialMap.delete B.ns nl) nl rp')
        l (readNRec bl nl p pg s src') := by
    rw [Iris.Std.LawfulPartialMap.insert_delete]
    simp [nodeAdded, parentAdd, hnl, hrp]; rfl
  unfold bktToks
  rw [if_neg hrn, hbv', if_neg hrn, hns_eq]
  have hrest : ([∗map] _y ↦ ry ∈ Iris.Std.PartialMap.delete B.ns nl, nodeToks (GF := GF) γ W B ry) ⊢
      [∗map] _y ↦ ry ∈ Iris.Std.PartialMap.delete B.ns nl,
        nodeToks (GF := GF) γ W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') ry := by
    apply BigSepM.bigSepM_mono
    intro y ry hy
    rw [Iris.Std.LawfulPartialMap.get?_delete] at hy
    split at hy
    · cases hy
    rename_i hyn
    refine nodeToks_congr γ W B _ ry ry rfl rfl rfl rfl ?_
    intro hlf x hx
    rw [hnm', if_neg]
    intro he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    have hpos2 : pagePosAt B y j w.pgid := ⟨ry, x, hy, hlf, hj, he, hnone⟩
    exact hc9 y j w.pgid nl i w.pgid hpos2 hpos
      (by intro h; simp only [Prod.mk.injEq] at h; exact hyn h.1.symm) _ hcself hcself
  have hfr : Iris.Std.PartialMap.get? (Iris.Std.PartialMap.insert
      (Iris.Std.PartialMap.delete B.ns nl) nl rp') l = none := by
    rw [Iris.Std.get?_insert_ne (Ne.symm hlnl), Iris.Std.LawfulPartialMap.get?_delete,
      if_neg (Ne.symm hlnl)]
    exact hfresh
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) hrp).1 $$ H
    with ⟨Hp, Hrest⟩
  ihave Hp := nodeToks_parent γ W B (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') rp rp'
    rfl rfl rfl rfl hbr i w hw hnone (by rw [hnm', if_pos rfl]; nofun) hnd
    (fun k hk => by rw [hnm', if_neg hk]) $$ Hp
  icases Hp with ⟨HX, Hp⟩
  ihave Hn := toks_newNode γ W hv (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') (opened B)
    rfl (uint.nat w.pgid) pg hpg (by rcases hkind with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])
    (readNRec bl nl p pg s src') src' rfl rfl
    (fun _ => by
      simp only [readNRec, readNodeV]; rw [hpid]
      exact uint_nat_W64_w _ (by have := w.pgid.isLt; unfold uint.nat; omega)) $$ HX
  ihave Hrest := hrest $$ Hrest
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W
    (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') r) hfr).2
  iframe Hn
  iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W
    (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') r) (Iris.Std.get?_delete_eq rfl)).2
  iframe

/-- An inline bucket's page as a node: no tokens. -/
theorem toks_inline (γ : GName) (W : WView) (B' : BRec) (ipg : List w8) (hg : inlineGood ipg)
    (r : NRec) (src : Src) (hws : r.ws = pageWs ipg src)
    (hleaf : r.nv.isLeaf' = decide (pageFlags ipg = leafPageFlag)) (hpid : r.nv.pgid' = W64 0) :
    ⊢ nodeToks (GF := GF) γ W B' r := by
  obtain ⟨-, hfl, -, -, hks⟩ := hg
  unfold nodeToks
  rw [hpid, if_pos rfl, hws, hleaf]
  simp only [hfl, _root_.decide_true, ↓reduceIte]
  refine emp_sep.2.trans (sep_mono .rfl ?_)
  unfold pageWs
  rw [BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_emp.2.trans (BigSepL.bigSepL_mono fun {k i} hk => ?_)
  have hi : i < pageCount ipg := List.mem_range.1 (List.mem_of_getElem? hk)
  rw [if_neg]
  rintro ⟨h1, -⟩
  have h2 := (isBkt_pageW ipg src i hfl).1 h1
  have h3 := (hks i hi).2
  unfold bucketLeafFlag at h2; omega

/-- Materializing the root of a bucket with no node keeps the bucket's tokens. -/
theorem bktToks_addRoot (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (l : Loc) (hl : l ≠ null)
    (pg : List w8)
    (hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg)
    (hpgi : B.ib.root' = W64 0 → pg = B.ipg) (p : Loc) (s cs' : GoSlice) (src' : Src) :
    bktToks (GF := GF) γ W B ⊢
      bktToks γ W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') := by
  obtain ⟨hc1, hc2, hc3, -⟩ := hc
  obtain ⟨hns0, -⟩ := hc3 hrn
  have hbv' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').bv.rootNode' = l := by
    simp [nodeAdded]
  have hns' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').ns =
      Iris.Std.PartialMap.insert B.ns l (readNRec bl null p pg s src') := by
    simp [nodeAdded, parentAdd]; rfl
  unfold bktToks
  rw [if_pos hrn, hbv', if_neg hl, hns']
  refine BIBase.Entails.trans ?_ (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W
    (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') r) (m := B.ns) (i := l)
    (x := readNRec bl null p pg s src') (by rw [hns0]; rfl)).2
  rw [hns0]
  refine BIBase.Entails.trans ?_ (sep_mono .rfl BigSepM.bigSepM_empty.2)
  refine BIBase.Entails.trans ?_ sep_emp.2
  by_cases hr : B.ib.root' = W64 0
  · rw [if_pos hr]
    obtain ⟨-, -, hg⟩ := hc1 hr hrn
    rw [hpgi hr]
    refine toks_inline γ W _ B.ipg hg _ src' rfl rfl ?_
    simp only [readNRec, readNodeV]; rw [hg.1]; rfl
  · rw [if_neg hr]
    have hpg := hpgf hr
    obtain ⟨-, hwf⟩ := hc2 hr
    obtain ⟨-, hpid, -, hkind⟩ := treeWF_page _ _ _ pg (hwf hrn) hpg
    exact toks_newNode γ W hv (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs')
      (opened B) rfl (uint.nat B.ib.root') pg hpg
      (by rcases hkind with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) (readNRec bl null p pg s src') src' rfl rfl
      (fun _ => by
        simp only [readNRec, readNodeV]; rw [hpid]
        exact uint_nat_W64_w _ (by have := B.ib.root'.isLt; unfold uint.nat; omega))

end bkttoks

/-! ### Keys -/

section keys
variable [ext : FfiSyntax]

theorem keyIn_none (k : List w8) : keyIn none none k := by
  unfold keyIn keyGe keyLt
  exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem inodeOf_key_ne_nil (p : Loc) (pg : List w8) (hrd : pageReadable pg) (hc : 0 < pageCount pg) :
    (inodeOf p pg 0).key' ≠ slice.nil := by
  intro he
  have hl := congrArg GoSlice.len he
  unfold inodeOf at hl
  split at hl
  · rename_i hf
    have h1 := (hrd.2.1 hf).2 0 hc
    have h2 : leafKsize pg 0 < 2 ^ 32 := leAt_lt _ _ 4
    simp only [slice.nil] at hl
    have h4 : uint.Z (W64 (leafKsize pg 0 : Int)) = 0 := by rw [hl]; rfl
    have h3 : uint.Z (W64 (leafKsize pg 0 : Int)) = leafKsize pg 0 := by word
    omega
  · rename_i hf
    have h1 := ((hrd.2.2 hf).2 0 hc).2.2
    have h2 : branchKsize pg 0 < 2 ^ 32 := leAt_lt _ _ 4
    simp only [slice.nil] at hl
    have h4 : uint.Z (W64 (branchKsize pg 0 : Int)) = 0 := by rw [hl]; rfl
    have h3 : uint.Z (W64 (branchKsize pg 0 : Int)) = branchKsize pg 0 := by word
    omega

/-- A node's keys in a bucket that grew by the node `l` of the position `c` (see the clauses'
hypotheses). -/
theorem nodeKeys_frame (W : WView) (B B' : BRec) (bnd bnd' : Loc → Option (List w8) × Option (List w8))
    (y : Loc) (ry ry' : NRec) (h : nodeKeys W B bnd y ry) (hb : bnd' y = bnd y)
    (hbp : ry.nv.parent' ≠ null → bnd' ry.nv.parent' = bnd ry.nv.parent')
    (hws : ry'.ws = ry.ws) (hpar : ry'.nv.parent' = ry.nv.parent') (hleaf : ry'.nv.isLeaf' = ry.nv.isLeaf')
    (hkey' : ry'.nv.key' = ry.nv.key') (hkey : ry'.key = ry.key) (hpgid : ry'.nv.pgid' = ry.nv.pgid')
    (hunb : ry'.nv.unbalanced' = ry.nv.unbalanced')
    (hns : ∀ z rz, B.ns !! z = some rz → ∃ rz', B'.ns !! z = some rz' ∧ rz'.ws = rz.ws ∧
      rz'.nv.isLeaf' = rz.nv.isLeaf')
    (hnmB : ∀ k l', B'.nm !! k = some l' → B.nm !! k = some l' ∨ (B.nm !! k = none ∧
      ∃ r', B'.ns !! l' = some r' ∧ ∀ pg, W.pages !! uint.nat k = some pg →
        r'.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)))
    (hnmN : ∀ k, B'.nm !! k = none → B.nm !! k = none) : nodeKeys W B' bnd' y ry' := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨by rw [hws, hb]; exact c1, by rw [hpar, hb]; exact c2, ?_, ?_,
    by rw [hleaf, hunb, hpar, hws]; exact c5, by rw [hleaf, hws]; exact c6⟩
  · intro hp
    rw [hpar] at hp
    obtain ⟨hk', rp0, i0, w0, hrp0, hw0, hpg0, hkey0, hbnd0⟩ := c3 hp
    obtain ⟨rp0', h1, h2, -⟩ := hns _ _ hrp0
    refine ⟨by rw [hkey']; exact hk', rp0', i0, w0, by rw [hpar]; exact h1, by rw [h2]; exact hw0,
      by rw [hpgid]; exact hpg0, by rw [hkey]; exact hkey0, ?_⟩
    rw [hb, hpar, hbp hp, h2]; exact hbnd0
  · intro hlf
    rw [hleaf] at hlf
    obtain ⟨h2, kind, hkd⟩ := c4 hlf
    refine ⟨by rw [hws]; exact h2, kind, fun j w' hj => ?_⟩
    rw [hws] at hj
    obtain ⟨ha, hbb⟩ := hkd j w' hj
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rcases hnmB _ _ hl' with ho | ⟨hn0, r', hr', hlf'⟩
      · obtain ⟨r'', h1, h2⟩ := ha l' ho
        obtain ⟨r3, h3, -, h4⟩ := hns _ _ h1
        exact ⟨r3, h3, h4.trans h2⟩
      · obtain ⟨pg0, hpg0, -, hk0, -⟩ := hbb hn0
        exact ⟨r', hr', by rw [hlf' pg0 hpg0]; exact hk0⟩
    · obtain ⟨pg0, a1, a2, a3, a4, a5⟩ := hbb (hnmN _ hn)
      exact ⟨pg0, a1, a2, a3, a4, by rw [hb, hws]; exact a5⟩

/-- The keys of a node read from the page `pg` of the position `c` whose tree has the bounds
`b`, its children not materialized (all but the parent clauses). -/
theorem nodeKeys_page (W : WView) (B' : BRec) (bnd' : Loc → Option (List w8) × Option (List w8))
    (l : Loc) (r : NRec) (c : Nat) (pg : List w8) (src : Src) (b : Option (List w8) × Option (List w8))
    (hpg : W.pages !! c = some pg) (htk : treeKeys W.pages c b.1 b.2) (hws : r.ws = pageWs pg src)
    (hleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)) (hb : bnd' l = b)
    (hfree : ∀ j < pageCount pg, pageFlags pg = branchPageFlag →
      (W.pages !! branchPgid pg j).isSome → B'.nm !! W64 (branchPgid pg j : Int) = none) :
    (∀ w ∈ r.ws, keyIn (bnd' l).1 (bnd' l).2 w.key) ∧
    (r.nv.isLeaf' = false → 2 ≤ r.ws.length ∧ ∃ kind : Bool, ∀ i w, r.ws[i]? = some w →
      (∀ l', B'.nm !! w.pgid = some l' → ∃ r', B'.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
      (B'.nm !! w.pgid = none → ∃ pg, W.pages !! uint.nat w.pgid = some pg ∧ 0 < pageCount pg ∧
        decide (pageFlags pg = leafPageFlag) = kind ∧ pageKey pg 0 = w.key ∧
        treeKeys W.pages (uint.nat w.pgid) (entryBnd (bnd' l) r.ws i).1 (entryBnd (bnd' l) r.ws i).2)) ∧
    (r.nv.isLeaf' = true → ∀ w ∈ r.ws, isBktFlag w.flags → inBucketRoot w.value ≠ 0 →
      treeKeys W.pages (inBucketRoot w.value) none none) := by
  rw [hb, hws]
  refine ⟨treeKeys_pageWs W.pages c b.1 b.2 pg src htk hpg, ?_, ?_⟩
  · intro hlf
    rw [hleaf] at hlf
    have hnl : pageFlags pg ≠ leafPageFlag := by simpa using hlf
    cases htk with
    | leaf _ pg' _ _ hpg' hl _ _ => rw [hpg] at hpg'; cases hpg'; exact absurd hl hnl
    | branch _ pg' _ _ kindN hpg' hbr h2 _ hch hsub =>
      rw [hpg] at hpg'; cases hpg'
      refine ⟨by rw [pageWs_length]; exact h2, decide (kindN = leafPageFlag), fun j w' hj => ?_⟩
      rw [pageWs_get] at hj
      split at hj
      · rename_i hjl
        cases hj
        obtain ⟨cpg, hcpg, hcc, hcf, hck⟩ := hch j hjl
        have hnm := hfree j hjl hbr (by rw [hcpg]; rfl)
        obtain ⟨hk1, hp1⟩ := pageW_branch pg src j hnl
        rw [hp1]
        refine ⟨fun l' hl' => (by rw [hnm] at hl'; cases hl'), fun _ => ⟨cpg, ?_, hcc, by rw [hcf], ?_, ?_⟩⟩
        · rw [uint_nat_W64_w _ (branchPgid_lt pg j)]; exact hcpg
        · rw [hk1]; exact hck
        · rw [uint_nat_W64_w _ (branchPgid_lt pg j), entryBnd_pageWs b pg src j hjl hnl]
          exact hsub j hjl
      · cases hj
  · intro hlf w' hw' hbk hroot
    rw [hleaf] at hlf
    have hl : pageFlags pg = leafPageFlag := by simpa using hlf
    obtain ⟨j, hj, rfl⟩ := pageWs_mem pg src w' hw'
    cases htk with
    | leaf _ pg' _ _ hpg' _ _ hbkt =>
      rw [hpg] at hpg'; cases hpg'
      rw [(pageW_leaf pg src j hl).2.1] at hroot ⊢
      exact hbkt j hj ((isBkt_pageW pg src j hl).1 hbk) hroot
    | branch _ pg' _ _ _ hpg' hbr _ _ _ _ =>
      rw [hpg] at hpg'; cases hpg'
      rw [hl] at hbr; exact absurd hbr.symm branch_ne_leaf

end keys

/-! ### The materialized bucket -/

section mat
variable [ext : FfiSyntax]

/-- A child of a branch page is not the page itself. -/
theorem child_ne_self (W : WView) (hv : viewOK W) (c : Nat) (pg : List w8)
    (hpg : W.pages !! c = some pg) (hb : pageFlags pg = branchPageFlag) (j : Nat)
    (hj : j < pageCount pg) (hs : (W.pages !! branchPgid pg j).isSome) : branchPgid pg j ≠ c := by
  intro he
  obtain ⟨cpg, hcpg⟩ := Option.isSome_iff_exists.1 hs
  have := treeHas_self _ _ cpg hcpg
  rw [he] at this
  exact (hv.2.2.2.2.2.1 c pg hpg hb).2 j hj (he ▸ this)

theorem ownHas_some {pages : GMap Nat (List w8)} {a b : Nat} (h : ownHas pages a b) :
    (pages !! a).isSome := by
  cases h with
  | root _ pg hpg => rw [hpg]; rfl
  | child _ pg _ _ hpg _ _ _ => rw [hpg]; rfl

/-- The old nodes' records after a child is materialized. -/
theorem ns_addChild (B : BRec) (c : w64) (nl l : Loc) (r : NRec) (cs' : GoSlice) (rp : NRec)
    (hnl : nl ≠ null) (hrp : B.ns !! nl = some rp) (hfresh : B.ns !! l = none) :
    ∀ y ry, B.ns !! y = some ry → ∃ ry', (nodeAdded B c nl l r cs').ns !! y = some ry' ∧
      ry'.ws = ry.ws ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.nv.parent' = ry.nv.parent' ∧
      ry'.nv.key' = ry.nv.key' ∧ ry'.key = ry.key ∧ ry'.nv.pgid' = ry.nv.pgid' ∧
      ry'.nv.unbalanced' = ry.nv.unbalanced' := by
  intro y ry hy
  have hyl : y ≠ l := by intro h; rw [h, hfresh] at hy; cases hy
  rw [nodeAdded_ns B c nl l r cs' rp hnl hrp, if_neg hyl]
  by_cases hyn : y = nl
  · subst hyn; rw [hrp] at hy; cases hy
    exact ⟨({ rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [l] } : NRec),
      by rw [if_pos rfl], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg hyn]; exact ⟨ry, hy, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An entry on a page of the materialized position `c`: in its node, or on a page of one of
its children's positions. -/
theorem entryIn_pos (W : WView) (B' : BRec) (l : Loc) (r : NRec) (c : Nat) (pg : List w8) (src : Src)
    (hpg : W.pages !! c = some pg) (hr : B'.ns !! l = some r) (hws : r.ws = pageWs pg src)
    (hleaf : r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag))
    (hfree : ∀ j < pageCount pg, pageFlags pg = branchPageFlag →
      (W.pages !! branchPgid pg j).isSome → B'.nm !! W64 (branchPgid pg j : Int) = none)
    (k v : List w8) (q : Nat) (pgq : List w8) (j : Nat) (hown : ownHas W.pages c q)
    (hpq : W.pages !! q = some pgq) (hlq : pageFlags pgq = leafPageFlag) (hj : j < pageCount pgq)
    (hkq : leafKey pgq j = k) (hfq : leafFlags pgq j % 2 = bucketLeafFlag) (hvq : leafValue pgq j = v) :
    entryIn W B' k v := by
  rcases ownHas_cases pg hpg hown with rfl | ⟨hb, i', hi', hown'⟩
  · rw [hpg] at hpq; cases hpq
    obtain ⟨h1, h2, -⟩ := pageW_leaf pg src j hlq
    refine Or.inl ⟨l, r, pageW pg src j, hr, by rw [hleaf]; simp [hlq], ?_, by rw [h1]; exact hkq,
      (isBkt_pageW pg src j hlq).2 hfq, by rw [h2]; exact hvq⟩
    rw [hws]; exact List.mem_of_getElem? (by rw [pageWs_get, if_pos hj])
  · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hb]; exact branch_ne_leaf
    refine Or.inr ⟨branchPgid pg i', q, pgq, j, Or.inr ⟨l, i', ⟨r, pageW pg src i', hr,
      by rw [hleaf]; simp [hnl], by rw [hws, pageWs_get, if_pos hi'], (pageW_branch pg src i' hnl).2,
      hfree i' hi' hb (ownHas_some hown')⟩, branchPgid_lt pg i'⟩, hown', hpq, hlq, hj, hkq, hfq, hvq⟩

section child
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none)
    (hnl : nl ≠ null) (pg : List w8) (hpg : W.pages !! uint.nat w.pgid = some pg) (p : Loc)
    (s cs' : GoSlice) (src' : Src)
include hv hc hrp hbr hw hnone hpg

theorem nm_addChild (k : w64) :
    (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! k =
      if k = w.pgid then some l else B.nm !! k := by
  show (<[w.pgid := l]> B.nm) !! k = _
  by_cases hk : k = w.pgid
  · subst hk; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]

theorem free_addChild : ∀ j < pageCount pg, pageFlags pg = branchPageFlag →
    (W.pages !! branchPgid pg j).isSome →
    (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').nm !! W64 (branchPgid pg j : Int) = none := by
  intro j hj hb hs
  have hpos : pagePosAt B nl i w.pgid := ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩
  obtain ⟨cpg, hcpg⟩ := Option.isSome_iff_exists.1 hs
  rw [nm_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hnone l pg hpg p s cs' src', if_neg]
  · exact hc.2.2.2.2.2.2.2.2.2 nl i w.pgid hpos _
      (treeHas_child _ _ pg hpg hb j hj _ (treeHas_self _ _ cpg hcpg))
  · intro he
    exact child_ne_self W hv _ pg hpg hb j hj hs
      ((W64_eq_iff_nat _ w.pgid (branchPgid_lt pg j)).1 he)

include hfresh hnl in
/-- Materializing the page position `w.pgid` (entry `i` of the branch node `nl`) keeps the keys,
the new node's bounds its entry's. -/
theorem keys_addChild (hrd : pageReadable pg) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : bktKeysB W B bnd) :
    bktKeysB W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
      (fun x => if x = l then entryBnd (bnd nl) rp.ws i else bnd x) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hc
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc3 h0).1; rw [this] at hrp; cases hrp
  have hbv' : (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs').bv = B.bv := by
    simp [nodeAdded, hnl]
  have hns' := nodeAdded_ns B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp
  have hnsB := ns_addChild B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh
  have hnm' := nm_addChild W hwm bl B hv ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩
    nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  have hfree := free_addChild W hwm bl B hv ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩
    nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  obtain ⟨-, -, -, hrpk4, -, -⟩ := hk3 nl rp hrp
  obtain ⟨-, kind, hkd⟩ := hrpk4 hbr
  obtain ⟨pg', hpg', hcnt, -, hkey0, htk⟩ := (hkd i w hw).2 hnone
  rw [hpg] at hpg'; cases hpg'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrp12, -⟩ := hc8 nl rp hrp
  obtain ⟨-, -, hkids⟩ := hrp12 hbr
  obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
  obtain ⟨-, hpid, -, -⟩ := treeWF_page _ _ _ pg (hcwf hnone) hpg
  -- the old nodes are in the bucket, and so are their parents
  have hold : ∀ x, (B.ns !! x).isSome → x ≠ l := by
    intro x hx he; rw [he, hfresh] at hx; cases hx
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → (B.ns !! ry.nv.parent').isSome := by
    intro y ry hy hp
    obtain ⟨rq, hrq, -⟩ := (hc8 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
    rw [hrq]; rfl
  have hframe : ∀ y ry ry', B.ns !! y = some ry → ry'.ws = ry.ws →
      ry'.nv.parent' = ry.nv.parent' → ry'.nv.isLeaf' = ry.nv.isLeaf' → ry'.nv.key' = ry.nv.key' →
      ry'.key = ry.key → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      nodeKeys W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs')
        (fun x => if x = l then entryBnd (bnd nl) rp.ws i else bnd x) y ry' := by
    intro y ry ry' hy h1 h2 h3 h4 h5 h6 h7
    refine nodeKeys_frame W B _ bnd _ y ry ry' (hk3 y ry hy)
      (by rw [if_neg (hold y (by rw [hy]; rfl))])
      (fun hp => by rw [if_neg (hold _ (hpar y ry hy hp))]) h1 h2 h3 h4 h5 h6 h7
      (fun z rz hz => by
        obtain ⟨rz', a, b, c, -⟩ := hnsB z rz hz; exact ⟨rz', a, b, c⟩) ?_ ?_
    · intro k l' hl'
      rw [hnm'] at hl'
      split at hl'
      · rename_i hkw
        cases hl'
        subst hkw
        refine Or.inr ⟨hnone, _, by rw [hns', if_pos rfl], fun pg0 h0 => ?_⟩
        rw [hpg] at h0; cases h0; rfl
      · exact Or.inl hl'
    · intro k hk0
      rw [hnm'] at hk0
      split at hk0
      · cases hk0
      · exact hk0
  refine ⟨fun h => by rw [hbv'] at h; exact hk1 h, ?_, ?_⟩
  · intro r0 h0
    rw [hbv'] at h0
    rw [hns'] at h0
    have hrs := hc4 hrn
    obtain ⟨-, rr, hrr, -⟩ := hc5 _ _ hrs
    rw [if_neg (hold _ (by rw [hrr]; rfl))] at h0
    split at h0
    · rename_i he
      cases h0
      rw [he] at hrr; rw [hrp] at hrr; cases hrr
      exact hk2 rp (he ▸ hrp)
    · exact hk2 r0 h0
  · intro y ry hy
    rw [hns'] at hy
    split at hy
    · rename_i hyl
      cases hy
      subst hyl
      obtain ⟨n1, n4, n6⟩ := nodeKeys_page W (nodeAdded B w.pgid nl y (readNRec bl nl p pg s src') cs')
        (fun x => if x = y then entryBnd (bnd nl) rp.ws i else bnd x) y
        (readNRec bl nl p pg s src') (uint.nat w.pgid) pg src' (entryBnd (bnd nl) rp.ws i) hpg htk rfl rfl
        (by simp) hfree
      refine ⟨n1, fun h => absurd h hnl, fun _ => ⟨?_, ({ rp with nv := { rp.nv with children' := cs' }, cs := rp.cs ++ [y] } : NRec),
        i, w, ?_, hw, ?_, ?_, ?_⟩, n4,
        fun _ _ _ => by show 0 < (pageWs pg src').length; rw [pageWs_length]; exact hcnt, n6⟩
      · show (if pageCount pg = 0 then slice.nil else (inodeOf p pg 0).key') ≠ slice.nil
        rw [if_neg (by omega)]; exact inodeOf_key_ne_nil p pg hrd hcnt
      · show (nodeAdded B w.pgid nl y (readNRec bl nl p pg s src') cs').ns !! nl = _
        rw [hns', if_neg (Ne.symm hlnl), if_pos rfl]
      · show w.pgid = W64 (pageId pg : Int)
        rw [hpid]; unfold uint.nat; word
      · show w.key = wKey (pageWs pg src') 0
        rw [wKey_pageWs_i _ _ 0 hcnt, pageW_key_pageKey]; exact hkey0.symm
      · show (if y = y then entryBnd (bnd nl) rp.ws i else bnd y) =
          entryBnd (if nl = y then entryBnd (bnd nl) rp.ws i else bnd nl) rp.ws i
        rw [if_pos rfl, if_neg (Ne.symm hlnl)]
    · rename_i hyl
      split at hy
      · rename_i hyn
        cases hy
        subst hyn
        exact hframe y rp _ hrp rfl rfl rfl rfl rfl rfl rfl
      · exact hframe y ry ry hy rfl rfl rfl rfl rfl rfl rfl

include hfresh hnl in
theorem entryIn_addChild (k v : List w8) (h : entryIn W B k v) :
    entryIn W (nodeAdded B w.pgid nl l (readNRec bl nl p pg s src') cs') k v := by
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hrp; cases hrp
  have hnsB := ns_addChild B w.pgid nl l (readNRec bl nl p pg s src') cs' rp hnl hrp hfresh
  have hnm' := nm_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hnone l pg hpg p s cs' src'
  rcases h with ⟨y, ry, w', hy, hlf, hmem, hk, hbk, hvv⟩ |
    ⟨c', q, pgq, j, hpos', hown, hpq, hlq, hj, hkq, hfq, hvq⟩
  · obtain ⟨ry', h1, h2, h3, -⟩ := hnsB y ry hy
    exact Or.inl ⟨y, ry', w', h1, by rw [h3]; exact hlf, by rw [h2]; exact hmem, hk, hbk, hvv⟩
  · rcases hpos' with ⟨hrn0, -⟩ | ⟨y, j0, hpp, hlt⟩
    · exact absurd hrn0 hrn
    by_cases hce : W64 (c' : Int) = w.pgid
    · have hcn : c' = uint.nat w.pgid := (W64_eq_iff_nat c' w.pgid hlt).1 hce
      subst hcn
      exact entryIn_pos W _ l _ _ pg src' hpg
        (by rw [nodeAdded_ns B w.pgid nl l _ cs' rp hnl hrp, if_pos rfl]) rfl rfl
        (free_addChild W hwm bl B hv hc nl rp i w hrp hbr hw hnone l pg hpg p s cs' src')
        k v q pgq j hown hpq hlq hj hkq hfq hvq
    · obtain ⟨ry, wy, hy, hyl, hwy, hwyp, hnmy⟩ := hpp
      obtain ⟨ry', h1, h2, h3, -⟩ := hnsB y ry hy
      refine Or.inr ⟨c', q, pgq, j, Or.inr ⟨y, j0, ⟨ry', wy, h1, by rw [h3]; exact hyl,
        by rw [h2]; exact hwy, hwyp, ?_⟩, hlt⟩, hown, hpq, hlq, hj, hkq, hfq, hvq⟩
      rw [hnm', if_neg hce]; exact hnmy

end child

/-- Materializing the root of a bucket with no node keeps the keys (the root has no bounds). -/
theorem keys_addRoot (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (l : Loc) (hl : l ≠ null)
    (pg : List w8)
    (hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg)
    (hpgi : B.ib.root' = W64 0 → pg = B.ipg) (p : Loc) (s cs' : GoSlice) (src' : Src)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd) :
    bktKeysB W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') (fun _ => (none, none)) := by
  obtain ⟨hc1, -, hc3, -⟩ := hc
  obtain ⟨hns0, hnm0⟩ := hc3 hrn
  have hns' := nodeAdded_root_ns B B.ib.root' l (readNRec bl null p pg s src') cs' hns0
  have hbv' : (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs').bv.rootNode' = l := by
    simp [nodeAdded]
  refine ⟨fun h => absurd (hbv' ▸ h) hl, fun r0 h0 => ?_, fun y ry hy => ?_⟩
  · rw [hbv', hns', if_pos rfl] at h0; cases h0; rfl
  rw [hns'] at hy
  split at hy
  · rename_i hyl
    cases hy
    subst hyl
    have hpar : ∀ x : Prop, (readNRec bl null p pg s src').nv.parent' ≠ null → x :=
      fun _ h => absurd rfl h
    by_cases hr : B.ib.root' = W64 0
    · obtain ⟨-, -, hg⟩ := hc1 hr hrn
      rw [hpgi hr]
      obtain ⟨-, hfl, -, -, hks⟩ := hg
      refine ⟨fun _ _ => keyIn_none _, fun _ => rfl, fun h => hpar _ h, fun hlf => ?_,
        fun _ _ h => hpar _ h, fun _ w' hw' hbk _ => ?_⟩
      · simp [readNRec, readNodeV, hfl] at hlf
      · obtain ⟨j, hj, rfl⟩ := pageWs_mem _ src' w' hw'
        have h2 := (isBkt_pageW _ src' j hfl).1 hbk
        have h3 := (hks j hj).2
        unfold bucketLeafFlag at h2; omega
    · have hpg := hpgf hr
      have htk := hk.1 hrn hr
      obtain ⟨n1, n4, n6⟩ := nodeKeys_page W (nodeAdded B B.ib.root' null y (readNRec bl null p pg s src') cs')
        (fun _ => (none, none)) y (readNRec bl null p pg s src') (uint.nat B.ib.root') pg src' (none, none)
        hpg htk rfl rfl rfl (fun j hj hb hs => by
          show (<[B.ib.root' := y]> B.nm) !! _ = none
          rw [GMap.lookup_insert_ne, hnm0]
          · rfl
          · intro he
            exact child_ne_self W hv _ pg hpg hb j hj hs
              ((W64_eq_iff_nat _ B.ib.root' (branchPgid_lt pg j)).1 he.symm))
      exact ⟨n1, fun _ => rfl, fun h => hpar _ h, n4, fun _ _ h => hpar _ h, n6⟩
  · cases hy

theorem entryIn_addRoot (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (l : Loc)
    (pg : List w8)
    (hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg)
    (p : Loc) (s cs' : GoSlice) (src' : Src) (k v : List w8) (h : entryIn W B k v) :
    entryIn W (nodeAdded B B.ib.root' null l (readNRec bl null p pg s src') cs') k v := by
  obtain ⟨-, -, hc3, -⟩ := hc
  obtain ⟨hns0, hnm0⟩ := hc3 hrn
  rcases h with ⟨y, ry, -, hy, -⟩ | ⟨c', q, pgq, j, hpos', hown, hpq, hlq, hj, hkq, hfq, hvq⟩
  · rw [hns0] at hy; cases hy
  rcases hpos' with ⟨-, hr, rfl⟩ | ⟨y, j0, ⟨ry, -, hy, -⟩, -⟩
  · have hpg := hpgf hr
    refine entryIn_pos W _ l _ _ pg src' hpg
      (by rw [nodeAdded_root_ns B B.ib.root' l _ cs' hns0, if_pos rfl]) rfl rfl ?_
      k v q pgq j hown hpq hlq hj hkq hfq hvq
    intro j hj hb hs
    show (<[B.ib.root' := l]> B.nm) !! _ = none
    rw [GMap.lookup_insert_ne, hnm0]
    · rfl
    · intro he
      exact child_ne_self W hv _ pg hpg hb j hj hs
        ((W64_eq_iff_nat _ B.ib.root' (branchPgid_lt pg j)).1 he.symm)
  · rw [hns0] at hy; cases hy

end mat

/-! ### `Bucket.node`'s result -/

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- What `b.node(pgid, parent)` does to the shape (`Bucket.node.sspec`): its tokens and keys go
to the new bucket, its nested buckets' entries stay, and the old nodes keep their bounds. -/
theorem bktShape_nodeRes (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (pm : GMap w64 Loc) (pgid : w64) (parent p : Loc) (pg : List w8) (src : Src) (l : Loc)
    (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hpre : B.nm !! pgid = none → nodeSrcOK W B pm pgid p pg src ∧
      ((parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨ ∃ i, pagePosAt B parent i pgid))
    (hres : nodeRes B bl pgid parent p pg src l B' st st') :
    bktShape (GF := GF) γ W B ⊢ bktShape γ W B' ∗
      ⌜(∀ k v, entryIn W B k v → entryIn W B' k v) ∧
        ∀ bnd, bktKeysB W B bnd → ∃ bnd', bktKeysB W B' bnd' ∧
          ∀ x, (B.ns !! x).isSome → bnd' x = bnd x⌝ := by
  rcases hres with ⟨-, rfl, -⟩ | ⟨hk, hfresh, hl, -, s, cs', src', -, -, rfl⟩
  · iintro H
    iframe
    ipureintro
    exact ⟨fun _ _ h => h, fun bnd h => ⟨bnd, h, fun _ _ => rfl⟩⟩
  obtain ⟨hsrc, hcase⟩ := hpre hk
  unfold bktShape
  rcases hcase with ⟨rfl, hrn, rfl⟩ | ⟨i, rp, w, hrp, hbr, hw, rfl, hnone⟩
  · have hpgf : B.ib.root' ≠ W64 0 → W.pages !! uint.nat B.ib.root' = some pg := fun hr =>
      (hsrc.2.2.2 (hc.2.2.2.2.2.1 hr)).2.2.1
    have hpgi : B.ib.root' = W64 0 → pg = B.ipg := fun hr =>
      (hsrc.2.2.1 (hc.1 hr hrn).1).2.2.1
    iintro ⟨Ht, %Hk⟩
    obtain ⟨bnd0, Hk⟩ := Hk
    isplitl [Ht]
    · isplitl [Ht]
      · iapply bktToks_addRoot γ W hwm bl B hv hc hrn l hl pg hpgf hpgi p s cs' src' $$ Ht
      · ipureintro
        exact ⟨_, keys_addRoot W hwm bl B hv hc hrn l hl pg hpgf hpgi p s cs' src' bnd0 Hk⟩
    · ipureintro
      refine ⟨entryIn_addRoot W hwm bl B hv hc hrn l pg hpgf p s cs' src', fun bnd hb =>
        ⟨_, keys_addRoot W hwm bl B hv hc hrn l hl pg hpgf hpgi p s cs' src' bnd hb, fun x hx => ?_⟩⟩
      rw [(hc.2.2.1 hrn).1] at hx; cases hx
  · have hroot : B.ib.root' ≠ W64 0 := by
      intro h0; have := hc.2.2.2.2.2.2.1 h0 parent rp hrp; rw [hbr] at this; cases this
    have hpg : W.pages !! uint.nat w.pgid = some pg := (hsrc.2.2.2 (hc.2.2.2.2.2.1 hroot)).2.2.1
    have hnl : parent ≠ null := by
      obtain ⟨-, -, -, -, -, -, h7, -⟩ := hc.2.2.2.2.2.2.2.1 parent rp hrp
      exact (hc.2.2.2.2.1 _ _ h7).1
    iintro ⟨Ht, %Hk⟩
    obtain ⟨bnd0, Hk⟩ := Hk
    isplitl [Ht]
    · isplitl [Ht]
      · iapply bktToks_addChild γ W hwm bl B hv hc parent rp i w hrp hbr hw hnone l hfresh hnl pg hpg
          p s cs' src' $$ Ht
      · ipureintro
        exact ⟨_, keys_addChild W hwm bl B hv hc parent rp i w hrp hbr hw hnone l hfresh hnl pg hpg
          p s cs' src' hsrc.1 bnd0 Hk⟩
    · ipureintro
      refine ⟨entryIn_addChild W hwm bl B hv hc parent rp i w hrp hbr hw hnone l hfresh hnl pg hpg
          p s cs' src', fun bnd hb => ⟨_, keys_addChild W hwm bl B hv hc parent rp i w hrp hbr hw
          hnone l hfresh hnl pg hpg p s cs' src' hsrc.1 bnd hb, fun x hx => ?_⟩⟩
      rw [if_neg]
      intro he; rw [he, hfresh] at hx; cases hx

end res

end bbolt
end EtcdGrove
end Perennial
