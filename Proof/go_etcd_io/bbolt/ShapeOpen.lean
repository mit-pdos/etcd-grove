/-
Opening a nested bucket keeps the write transaction's shape (`txShape`, `WriteTxShape.lean`).

`b.Bucket(k)` opens the nested bucket of `b`'s entry `k` (a new entry `k ↦ c` of `b.buckets`,
a new bucket record `C`): the tokens of that entry's tree (its root page's tree, if the bucket
is stored in pages) move from where they sit among `b`'s positions (a materialized leaf's
`nodeToks`, or a page position's or the root's `xPages`, from which an opened name's tree is
excluded) to `C`'s `bktToks` (`C` has no root node and no opened child, so its tokens are its
tree's). The disjointness of the tree left behind and the one moved is `viewUnique`: the
entry is reached from its position through branches (`ownHas`), the subtrees of a branch's
children are disjoint and do not contain the branch, and so are a leaf's nested buckets' trees
and the leaf. `C`'s keys are its tree's (`treeKeys`, from the bounds of the position the entry
is in), and the entry is `entryIn` of `b` (the cursor's path ends at it), so `bktNested` holds
of `k`.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.WriteBucket
public import Proof.go_etcd_io.bbolt.WriteCreate
public import Spec.go_etcd_io.bbolt.Cursor__seek_s

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace ShapeOpen

/-! ### Reaching pages -/

section reach
variable [ext : FfiSyntax]

theorem xHas_tree (pages : GMap Nat (List w8)) (op : List w8 → Prop) (c id : Nat)
    (h : xHas pages op c id) : treeHas pages c id := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas.sub r pg id hpg (pageHas.child pg i id hb hi ih)
  | bucket r pg i id hpg hl hi hf _ hbk => exact treeHas.sub r pg id hpg (pageHas.bucket pg i id hl hi hf hbk)

theorem xHas_mono (pages : GMap Nat (List w8)) (op op' : List w8 → Prop)
    (hop : ∀ k, op' k → op k) (c id : Nat) (h : xHas pages op c id) : xHas pages op' c id := by
  induction h with
  | root r pg hpg => exact xHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact xHas.child r pg i id hpg hb hi ih
  | bucket r pg i id hpg hl hi hf hn hbk =>
    exact xHas.bucket r pg i id hpg hl hi hf (fun h => hn (hop _ h)) hbk

theorem ownHas_tree (pages : GMap Nat (List w8)) (c p : Nat) (h : ownHas pages c p) :
    treeHas pages c p := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas.sub r pg id hpg (pageHas.child pg i id hb hi ih)

theorem ownHas_xHas (pages : GMap Nat (List w8)) (op : List w8 → Prop) (c p : Nat)
    (h : ownHas pages c p) (id : Nat) (hx : xHas pages op p id) : xHas pages op c id := by
  induction h with
  | root r pg hpg => exact hx
  | child r pg i id' hpg hb hi _ ih => exact xHas.child r pg i id hpg hb hi (ih hx)

/-- `treeHas` is transitive. -/
theorem treeHas_trans (pages : GMap Nat (List w8)) (a b d : Nat) (h : treeHas pages a b)
    (h2 : treeHas pages b d) : treeHas pages a d := by
  have key : ∀ a b, treeHas pages a b → treeHas pages b d → treeHas pages a d := by
    intro a b h
    induction h using treeHas.rec
      (motive_2 := fun pg b _ => treeHas pages b d → pageHas pages pg d)
      (motive_3 := fun v b _ => treeHas pages b d → bucketHas pages v d) with
    | root root pg hpg => exact fun h => h
    | sub r pg id hpg _ ih => exact fun h => treeHas.sub r pg d hpg (ih h)
    | child pg i id hb hi _ ih => exact pageHas.child pg i d hb hi (ih (by assumption))
    | bucket pg i id hl hi hf _ ih => exact pageHas.bucket pg i d hl hi hf (ih (by assumption))
    | file v id hr _ ih => exact bucketHas.file v d hr (ih (by assumption))
    | inline v id hr _ ih => exact bucketHas.inline v d hr (ih (by assumption))
  exact key a b h h2

theorem bucketHas_tree (pages : GMap Nat (List w8)) (p : Nat) (pg : List w8)
    (hpg : pages !! p = some pg) (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (d : Nat) (h : bucketHas pages (leafValue pg i) d) :
    treeHas pages p d :=
  treeHas.sub p pg d hpg (pageHas.bucket pg i d hl hi hf h)

theorem leaf_ne_branch (pg : List w8) (hl : pageFlags pg = leafPageFlag)
    (hb : pageFlags pg = branchPageFlag) : False := by
  rw [hl] at hb; exact absurd hb (by unfold leafPageFlag branchPageFlag; decide)

/-- The tree of a position `c` without the opened names `op'` (which include the name of the
entry `i` of the leaf `p` reached from `c` through branches) shares no page with that entry's
nested bucket. -/
theorem xHas_disj (pages : GMap Nat (List w8)) (hu : viewUnique pages) (op' : List w8 → Prop)
    (c p : Nat) (hown : ownHas pages c p) (pg : List w8) (hpg : pages !! p = some pg)
    (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (hop : op' (leafKey pg i)) (id : Nat)
    (hx : xHas pages op' c id) (hb : bucketHas pages (leafValue pg i) id) : False := by
  induction hown generalizing id with
  | root r pg0 hpg0 =>
    rw [hpg0] at hpg; cases hpg
    cases hx with
    | root _ _ _ => exact (hu.2 r pg hpg0 hl).2 i hi hf hb
    | child _ pg1 j _ hpg1 hb1 _ _ =>
      rw [hpg0] at hpg1; cases hpg1; exact leaf_ne_branch pg hl hb1
    | bucket _ pg1 j _ hpg1 _ hj hfj hnj hbj =>
      rw [hpg0] at hpg1; cases hpg1
      have hij : j ≠ i := by intro e; subst e; exact hnj hop
      exact (hu.2 r pg hpg0 hl).1 j i hj hi hij hfj hf id hbj hb
  | child r pg0 k p' hpg0 hb0 hk hown' ih =>
    have hkp : treeHas pages (branchPgid pg0 k) p' := ownHas_tree pages _ _ hown'
    have hkid : treeHas pages (branchPgid pg0 k) id :=
      treeHas_trans pages _ _ _ hkp (bucketHas_tree pages p' pg hpg hl i hi hf id hb)
    cases hx with
    | root _ _ _ => exact (hu.1 r pg0 hpg0 hb0).2 k hk hkid
    | child _ pg1 j _ hpg1 _ hj hxj =>
      rw [hpg0] at hpg1; cases hpg1
      by_cases e : j = k
      · subst e; exact ih hpg id hxj hb
      · exact (hu.1 r pg0 hpg0 hb0).1 j k hj hk e id (xHas_tree pages op' _ id hxj) hkid
    | bucket _ pg1 j _ hpg1 hl1 _ _ _ _ =>
      rw [hpg0] at hpg1; cases hpg1; exact leaf_ne_branch pg0 hl1 hb0

/-- The entry `i` of the leaf `p` reached from `c` through branches: its nested bucket's pages
are of `c`'s tree without the names `op` (which exclude its own). -/
theorem xHas_entry (pages : GMap Nat (List w8)) (op : List w8 → Prop)
    (c p : Nat) (hown : ownHas pages c p) (pg : List w8) (hpg : pages !! p = some pg)
    (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (hop : ¬ op (leafKey pg i)) (id : Nat)
    (hb : bucketHas pages (leafValue pg i) id) : xHas pages op c id :=
  ownHas_xHas pages op c p hown id (xHas.bucket p pg i id hpg hl hi hf hop hb)

end reach

/-! ### Tokens of page sets -/

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Classical in
/-- The pages of `pages` satisfying `P`. -/
def pagesWith (pages : GMap Nat (List w8)) (P : Nat → Prop) : GMap Nat (List w8) :=
  GMap.filter (fun id _ => decide (P id)) pages

theorem gmap_filter_eq (p : Nat → List w8 → Bool) (m : GMap Nat (List w8)) :
    GMap.filter p m = Iris.Std.PartialMap.filter p m := by
  refine GMap.ext (fun k => ?_)
  rw [GMap.lookup_filter]
  show _ = Iris.Std.PartialMap.get? (Iris.Std.PartialMap.filter p m) k
  rw [Iris.Std.LawfulPartialMap.get?_filter]
  change _ = (m !! k).bind _
  cases m !! k <;> rfl

open Classical in
theorem pgToks_with (γ : GName) (pages : GMap Nat (List w8)) (P : Nat → Prop) :
    pgToks (GF := GF) γ (pagesWith pages P) ⊣⊢
      [∗map] id ↦ _pg ∈ pages, if decide (P id) then iprop(id ↪[γ] ()) else emp := by
  unfold pgToks pagesWith
  rw [gmap_filter_eq]
  exact BiEntails.of_eq (BigSepM.bigSepM_filter_cond (Φ := fun id (_ : List w8) => iprop(id ↪[γ] ()))
    (fun id _ => decide (P id)))

open Classical in
/-- The tokens of the pages with `P` split into those of disjoint subsets. -/
theorem pgToks_split (γ : GName) (pages : GMap Nat (List w8)) (P Q1 Q2 : Nat → Prop)
    (h1 : ∀ id, Q1 id → P id) (h2 : ∀ id, Q2 id → P id) (hd : ∀ id, Q1 id → Q2 id → False) :
    pgToks (GF := GF) γ (pagesWith pages P) ⊢
      pgToks γ (pagesWith pages Q1) ∗ pgToks γ (pagesWith pages Q2) := by
  refine (pgToks_with γ pages P).1.trans ?_
  refine BIBase.Entails.trans ?_ (sep_mono (pgToks_with γ pages Q1).2 (pgToks_with γ pages Q2).2)
  refine BIBase.Entails.trans ?_ (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
  refine BigSepM.bigSepM_mono (fun {id _} _ => ?_)
  by_cases hp : P id
  · rw [decide_eq_true hp]
    by_cases hq1 : Q1 id
    · rw [decide_eq_true hq1, decide_eq_false (fun h => hd id hq1 h)]
      simp only [↓reduceIte]; exact sep_emp.2
    · rw [decide_eq_false hq1]
      by_cases hq2 : Q2 id
      · rw [decide_eq_true hq2]; simp only [↓reduceIte, Bool.false_eq_true]; exact emp_sep.2
      · rw [decide_eq_false hq2]; simp only [↓reduceIte, Bool.false_eq_true]
        exact Affine.affine.trans sep_emp.2
  · rw [decide_eq_false hp, decide_eq_false (fun h => hp (h1 id h)), decide_eq_false (fun h => hp (h2 id h))]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact sep_emp.2

open Classical in
/-- The tokens of fewer pages. -/
theorem pgToks_mono (γ : GName) (pages : GMap Nat (List w8)) (P Q : Nat → Prop)
    (h : ∀ id, Q id → P id) :
    pgToks (GF := GF) γ (pagesWith pages P) ⊢ pgToks γ (pagesWith pages Q) := by
  refine (pgToks_split γ pages P Q (fun _ => False) h (fun _ h => h.elim) (fun _ _ h => h)).trans ?_
  exact sep_elim_left

end toks

/-! ### Lists and maps of resources with one element changed -/

section bigops
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

theorem bigSepL_one {A : Type} (l : List A) (Φ Ψ : A → IProp GF) (R : IProp GF) (i : Nat) (x : A)
    (hx : l[i]? = some x) (hrest : ∀ y, Φ y ⊢ Ψ y) (hi : Φ x ⊢ Ψ x ∗ R) :
    ([∗list] y ∈ l, Φ y) ⊢ ([∗list] y ∈ l, Ψ y) ∗ R := by
  have h1 : ([∗list] y ∈ l, Φ y) ⊢ [∗list] k ↦ y ∈ l, iprop(Ψ y ∗ if k = i then R else emp) := by
    refine BigSepL.bigSepL_mono (fun {k y} hk => ?_)
    by_cases e : k = i
    · subst e; rw [hx] at hk; cases hk; rw [if_pos rfl]; exact hi
    · rw [if_neg e]; exact (hrest y).trans sep_emp.2
  refine h1.trans ((BigSepL.bigSepL_sep_eqv).1.trans (sep_mono .rfl ?_))
  refine (BigSepL.bigSepL_lookup_acc (Φ := fun k (_ : A) => iprop(if k = i then R else emp)) hx).1.trans ?_
  rw [if_pos rfl]; exact sep_elim_left

theorem bigSepM_one {V : Type} (m : GMap Loc V) (Φ Ψ : V → IProp GF) (R : IProp GF) (l : Loc)
    (x : V) (hx : m !! l = some x) (hrest : ∀ y, Φ y ⊢ Ψ y) (hi : Φ x ⊢ Ψ x ∗ R) :
    ([∗map] _k ↦ y ∈ m, Φ y) ⊢ ([∗map] _k ↦ y ∈ m, Ψ y) ∗ R := by
  refine (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ y => Φ y)
    (show Std.get? m l = some x from hx)).1.trans ?_
  refine BIBase.Entails.trans ?_ (sep_mono (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun _ y => Ψ y) (show Std.get? m l = some x from hx)).2 .rfl)
  refine (sep_mono hi (BigSepM.bigSepM_mono (fun {_ y} _ => hrest y))).trans ?_
  iintro ⟨⟨H1, H2⟩, H3⟩
  iframe

end bigops

/-! ### The tokens of a bucket opening an entry -/

section btoks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The tokens of the tree of a nested bucket's value `v` (none for an inline bucket). -/
def vToks (γ : GName) (W : WView) (v : List w8) : IProp GF :=
  if inBucketRoot v = 0 then emp else pgToks γ (pagesWith W.pages (treeHas W.pages (inBucketRoot v)))

/-- The bucket `B` with its entry `k` opened as the bucket `cl`. -/
def bOpen (B : BRec) (k : List w8) (cl : Loc) : BRec := { B with bm := <[k := cl]> B.bm }

theorem bOpen_bv (B : BRec) (k : List w8) (cl : Loc) : (bOpen B k cl).bv = B.bv := rfl
theorem bOpen_ib (B : BRec) (k : List w8) (cl : Loc) : (bOpen B k cl).ib = B.ib := rfl
theorem bOpen_ns (B : BRec) (k : List w8) (cl : Loc) : (bOpen B k cl).ns = B.ns := rfl
theorem bOpen_nm (B : BRec) (k : List w8) (cl : Loc) : (bOpen B k cl).nm = B.nm := rfl

theorem opened_bOpen (B : BRec) (k : List w8) (cl : Loc) (k' : List w8) :
    opened (bOpen B k cl) k' ↔ opened B k' ∨ k' = k := by
  unfold opened bOpen; simp only
  by_cases h : k' = k
  · subst h; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h]

theorem opened_bOpen_mono (B : BRec) (k : List w8) (cl : Loc) (k' : List w8) (h : opened B k') :
    opened (bOpen B k cl) k' := (opened_bOpen B k cl k').2 (Or.inl h)

/-- A position's tokens, the entry `i` of the leaf `p` it reaches through branches opened. -/
theorem toks_pos_split (γ : GName) (W : WView) (hu : viewUnique W.pages) (B : BRec) (cl : Loc)
    (c p : Nat) (hown : ownHas W.pages c p) (pg : List w8) (hpg : W.pages !! p = some pg)
    (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (hnb : ¬ opened B (leafKey pg i)) :
    pgToks (GF := GF) γ (xPages W.pages (opened B) c) ⊢
      pgToks γ (xPages W.pages (opened (bOpen B (leafKey pg i) cl)) c) ∗
        vToks γ W (leafValue pg i) := by
  have hop := opened_bOpen_mono B (leafKey pg i) cl
  unfold vToks
  by_cases hr : inBucketRoot (leafValue pg i) = 0
  · rw [if_pos hr]
    exact (pgToks_mono γ W.pages (xHas W.pages (opened B) c)
      (xHas W.pages (opened (bOpen B (leafKey pg i) cl)) c)
      (fun id h => xHas_mono W.pages _ _ hop c id h)).trans sep_emp.2
  · rw [if_neg hr]
    exact pgToks_split γ W.pages (xHas W.pages (opened B) c)
      (xHas W.pages (opened (bOpen B (leafKey pg i) cl)) c) (treeHas W.pages (inBucketRoot (leafValue pg i)))
      (fun id h => xHas_mono W.pages _ _ hop c id h)
      (fun id h => xHas_entry W.pages (opened B) c p hown pg hpg hl i hi hf hnb id
        (bucketHas.file _ id hr h))
      (fun id h1 h2 => xHas_disj W.pages hu _ c p hown pg hpg hl i hi hf
        ((opened_bOpen B _ cl _).2 (Or.inr rfl)) id h1 (bucketHas.file _ id hr h2))

open Classical in
/-- An entry's tokens, in a bucket that opened more names. -/
theorem etoks_mono (γ : GName) (W : WView) (B B' : BRec) (hnm : B'.nm = B.nm)
    (hop : ∀ k, opened B k → opened B' k) (r : NRec) (w : WEntry) :
    (if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks (GF := GF) γ (treePages W.pages (inBucketRoot w.value)) else emp)
      else (if B.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
        else emp)) ⊢
    (if r.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B' w.key then
          pgToks (GF := GF) γ (treePages W.pages (inBucketRoot w.value)) else emp)
      else (if B'.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B') (uint.nat w.pgid))
        else emp)) := by
  by_cases hleaf : r.nv.isLeaf' = true
  · rw [if_pos hleaf, if_pos hleaf]
    by_cases h' : isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B' w.key
    · rw [if_pos h', if_pos ⟨h'.1, h'.2.1, fun h => h'.2.2 (hop _ h)⟩]
    · rw [if_neg h']; exact Affine.affine
  · rw [if_neg hleaf, if_neg hleaf, hnm]
    by_cases hn : B.nm !! w.pgid = none
    · rw [if_pos hn, if_pos hn]
      exact pgToks_mono γ W.pages (xHas W.pages (opened B) (uint.nat w.pgid))
        (xHas W.pages (opened B') (uint.nat w.pgid)) (fun id h => xHas_mono W.pages _ _ hop _ id h)
    · rw [if_neg hn, if_neg hn]

theorem nodeToks_mono (γ : GName) (W : WView) (B B' : BRec) (hnm : B'.nm = B.nm)
    (hop : ∀ k, opened B k → opened B' k) (r : NRec) :
    nodeToks (GF := GF) γ W B r ⊢ nodeToks γ W B' r := by
  unfold nodeToks
  exact sep_mono .rfl (BigSepL.bigSepL_mono (fun {_ w} _ => etoks_mono γ W B B' hnm hop r w))

/-- A leaf node's tokens, its entry `i` (a nested bucket named `w.key`) opened. -/
theorem nodeToks_leaf_open (γ : GName) (W : WView) (B : BRec) (cl : Loc) (r : NRec)
    (hleaf : r.nv.isLeaf' = true) (i : Nat) (w : WEntry) (hw : r.ws[i]? = some w)
    (hf : isBktFlag w.flags) (hnb : ¬ opened B w.key) :
    nodeToks (GF := GF) γ W B r ⊢ nodeToks γ W (bOpen B w.key cl) r ∗ vToks γ W w.value := by
  unfold nodeToks
  refine (sep_mono .rfl (bigSepL_one r.ws _ _ _ i w hw
    (fun y => etoks_mono γ W B (bOpen B w.key cl) rfl (opened_bOpen_mono B w.key cl) r y) ?_)).trans
    sep_assoc.2
  rw [if_pos hleaf, if_pos hleaf,
    if_neg (show ¬ (isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened (bOpen B w.key cl) w.key)
      from fun h => h.2.2 ((opened_bOpen B w.key cl w.key).2 (Or.inr rfl)))]
  unfold vToks
  by_cases hr : inBucketRoot w.value = 0
  · rw [if_neg (show ¬ (isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key)
      from fun h => h.2.1 hr), if_pos hr]; exact sep_emp.2
  · rw [if_pos (show (isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key)
      from ⟨hf, hr, hnb⟩), if_neg hr]; exact emp_sep.2

/-- A branch node's tokens, an entry of a leaf page under its child `j` opened. -/
theorem nodeToks_branch_open (γ : GName) (W : WView) (hu : viewUnique W.pages) (B : BRec)
    (cl : Loc) (r : NRec) (hbr : r.nv.isLeaf' = false) (j : Nat) (wj : WEntry)
    (hwj : r.ws[j]? = some wj) (hnm : B.nm !! wj.pgid = none) (p : Nat)
    (hown : ownHas W.pages (uint.nat wj.pgid) p) (pg : List w8) (hpg : W.pages !! p = some pg)
    (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (hnb : ¬ opened B (leafKey pg i)) :
    nodeToks (GF := GF) γ W B r ⊢
      nodeToks γ W (bOpen B (leafKey pg i) cl) r ∗ vToks γ W (leafValue pg i) := by
  unfold nodeToks
  refine (sep_mono .rfl (bigSepL_one r.ws _ _ _ j wj hwj
    (fun y => etoks_mono γ W B (bOpen B (leafKey pg i) cl) rfl (opened_bOpen_mono B _ cl) r y) ?_)).trans
    sep_assoc.2
  have hleaf : ¬ r.nv.isLeaf' = true := by rw [hbr]; decide
  have hnm' : (bOpen B (leafKey pg i) cl).nm !! wj.pgid = none := hnm
  rw [if_neg hleaf, if_neg hleaf, if_pos hnm, if_pos hnm']
  exact toks_pos_split γ W hu B cl _ p hown pg hpg hl i hi hf hnb

/-- A bucket's tokens, its entry `k` (value `v`) opened. -/
theorem bktToks_open (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (cl : Loc)
    (k v : List w8) (hc : bktClean W hwm bl B) (hvw : viewOK W) (hnb : ¬ opened B k)
    (he : entryIn W B k v) :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W (bOpen B k cl) ∗ vToks γ W v := by
  have hu : viewUnique W.pages := hvw.2.2.2.2.2
  unfold bktToks
  rw [bOpen_bv, bOpen_ib, bOpen_ns]
  by_cases hrn : B.bv.rootNode' = null
  · rw [if_pos hrn, if_pos hrn]
    have hns := (hc.2.2.1 hrn).1
    rcases he with ⟨l, r, w, hr, -⟩ | ⟨c, p, pg, i, hpos, hown, hpg, hl, hi, hkey, hf, hval⟩
    · rw [hns, GMap.lookup_empty] at hr; cases hr
    · rcases hpos with ⟨-, hr0, rfl⟩ | ⟨l, j, ⟨r, w, hr, -⟩, -⟩
      · rw [if_neg hr0, if_neg hr0]
        subst hkey hval
        exact toks_pos_split γ W hu B cl _ p hown pg hpg hl i hi hf hnb
      · rw [hns, GMap.lookup_empty] at hr; cases hr
  · rw [if_neg hrn, if_neg hrn]
    rcases he with ⟨l, r, w, hr, hleaf, hmem, hkey, hf, hval⟩ |
      ⟨c, p, pg, i, hpos, hown, hpg, hl, hi, hkey, hf, hval⟩
    · obtain ⟨i, hw⟩ := List.mem_iff_getElem?.1 hmem
      subst hkey hval
      exact bigSepM_one B.ns (nodeToks γ W B) (nodeToks γ W (bOpen B w.key cl)) _ l r hr
        (nodeToks_mono γ W B _ rfl (opened_bOpen_mono B w.key cl))
        (nodeToks_leaf_open γ W B cl r hleaf i w hw hf hnb)
    · rcases hpos with ⟨h, -⟩ | ⟨lb, j, ⟨rb, wj, hrb, hbr, hwj, hpj, hnm⟩, hlt⟩
      · exact absurd h hrn
      · subst hkey hval
        have hc' : uint.nat wj.pgid = c := by rw [hpj]; exact uint_nat_W64_w c hlt
        rw [← hpj] at hnm
        rw [← hc'] at hown
        exact bigSepM_one B.ns (nodeToks γ W B) (nodeToks γ W (bOpen B (leafKey pg i) cl)) _ lb rb hrb
          (nodeToks_mono γ W B _ rfl (opened_bOpen_mono B _ cl))
          (nodeToks_branch_open γ W hu B cl rb hbr j wj hwj hnm p hown pg hpg hl i hi hf hnb)

/-- The opened bucket's tokens: its tree's. -/
theorem bktToks_child (γ : GName) (W : WView) (txl ibl pgl : Loc) (bm nm : GoMap) (v : List w8)
    (src : Src) :
    vToks (GF := GF) γ W v ⊢ bktToks γ W (childRec txl ibl pgl bm nm v src) := by
  unfold bktToks vToks
  have hrn : (childRec txl ibl pgl bm nm v src).bv.rootNode' = null := rfl
  have hib : (childRec txl ibl pgl bm nm v src).ib = ibOf v := rfl
  rw [if_pos hrn, hib]
  by_cases hr : inBucketRoot v = 0
  · rw [if_pos hr, if_pos ((ibOf_root_zero v).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((ibOf_root_zero v).1 h)), uint_nat_ibOf_root]
    exact pgToks_mono γ W.pages _ _ (fun id h => xHas_tree W.pages _ _ id h)

end btoks

/-! ### The transaction's shape, a bucket opened -/

section txadd
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

theorem entryIn_bOpen (W : WView) (B : BRec) (k : List w8) (cl : Loc) (k' v : List w8) :
    entryIn W (bOpen B k cl) k' v ↔ entryIn W B k' v := Iff.rfl

theorem bktKeys_bOpen (W : WView) (B : BRec) (k : List w8) (cl : Loc) :
    bktKeys W (bOpen B k cl) ↔ bktKeys W B := Iff.rfl

/-- The facts of the transaction with the bucket `bl`'s entry `k` (value `v`) opened as the new
bucket `cl` (record `Bc`). -/
theorem txFacts_add (W : WView) (T : WTx) (st : TxStats) (bl : Loc) (B : BRec) (k : List w8)
    (cl : Loc) (Bc : BRec) (v : List w8) (hB : T.bs !! bl = some B) (hfr : T.bs !! cl = none)
    (hent : entryIn W B k v) (h16 : 16 ≤ v.length) (hcib : Bc.ib = ibOf v)
    (hcbm : Bc.bm = ∅) (hcns : Bc.ns = ∅)
    (hkeys : inBucketRoot v ≠ 0 → treeKeys W.pages (inBucketRoot v) none none)
    (hf : ∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B) :
    ∀ b C, (wtxAdd T st bl (bOpen B k cl) cl Bc).bs !! b = some C →
      bktKeys W C ∧ bktNested W (wtxAdd T st bl (bOpen B k cl) cl Bc) C := by
  have hlk : ∀ y, (wtxAdd T st bl (bOpen B k cl) cl Bc).bs !! y =
      if y = cl then some Bc else if y = bl then some (bOpen B k cl) else T.bs !! y := by
    intro y
    show (<[cl := Bc]> (<[bl := bOpen B k cl]> T.bs)) !! y = _
    by_cases h1 : y = cl
    · subst h1; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h1), if_neg h1]
      by_cases h2 : y = bl
      · subst h2; rw [GMap.lookup_insert, if_pos rfl]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm h2), if_neg h2]
  have htgt : ∀ c C0, T.bs !! c = some C0 → ∃ C1,
      (wtxAdd T st bl (bOpen B k cl) cl Bc).bs !! c = some C1 ∧ C1.ib = C0.ib ∧ C1.bv = C0.bv := by
    intro c C0 h0
    have hc : c ≠ cl := by intro e; rw [e, hfr] at h0; cases h0
    rw [hlk, if_neg hc]
    by_cases e : c = bl
    · subst e; rw [hB] at h0; cases h0; exact ⟨bOpen B k cl, by rw [if_pos rfl], rfl, rfl⟩
    · exact ⟨C0, by rw [if_neg e]; exact h0, rfl, rfl⟩
  have hn1 : ∀ C k' c, bktNested W T C → C.bm !! k' = some c → ∃ C1 v',
      (wtxAdd T st bl (bOpen B k cl) cl Bc).bs !! c = some C1 ∧ entryIn W C k' v' ∧
      16 ≤ v'.length ∧ C1.ib.root' = (ibOf v').root' ∧ (C1.bv.rootNode' = null → C1.ib = ibOf v') := by
    intro C k' c hn hkc
    obtain ⟨C0, v', h0, h1, h2, h3, h4⟩ := hn k' c hkc
    obtain ⟨C1, h5, h6, h7⟩ := htgt c C0 h0
    exact ⟨C1, v', h5, h1, h2, by rw [h6]; exact h3, fun h => by rw [h6]; exact h4 (by rw [← h7]; exact h)⟩
  intro b C hC
  rw [hlk] at hC
  by_cases e1 : b = cl
  · rw [if_pos e1] at hC; cases hC
    refine ⟨⟨fun _ => (none, none), fun _ hr => ?_, fun r h => ?_, fun l r h => ?_⟩, fun k' c h => ?_⟩
    · have hr' : inBucketRoot v ≠ 0 := fun h => hr (by rw [hcib]; exact (ibOf_root_zero v).2 h)
      rw [hcib, uint_nat_ibOf_root]; exact hkeys hr'
    · rw [hcns, GMap.lookup_empty] at h; cases h
    · rw [hcns, GMap.lookup_empty] at h; cases h
    · rw [hcbm, GMap.lookup_empty] at h; cases h
  · rw [if_neg e1] at hC
    by_cases e2 : b = bl
    · rw [if_pos e2] at hC; cases hC
      refine ⟨(hf bl B hB).1, fun k' c hkc => ?_⟩
      by_cases ek : k' = k
      · subst ek
        have : c = cl := by
          have h := hkc; unfold bOpen at h; simp only at h
          rw [GMap.lookup_insert] at h; exact (Option.some.inj h).symm
        subst this
        exact ⟨Bc, v, by rw [hlk, if_pos rfl], hent, h16, by rw [hcib], fun _ => hcib⟩
      · have h : B.bm !! k' = some c := by
          have h := hkc; unfold bOpen at h; simp only at h
          rwa [GMap.lookup_insert_ne _ _ (Ne.symm ek)] at h
        exact hn1 B k' c (hf bl B hB).2 h
    · rw [if_neg e2] at hC
      exact ⟨(hf b C hC).1, fun k' c hkc => hn1 C k' c (hf b C hC).2 hkc⟩

end txadd

section txadd2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The transaction's shape, the bucket `bl`'s entry `k` opened as the new bucket `cl`. -/
theorem txShape_add (γ : GName) (W : WView) (T : WTx) (st : TxStats) (bl : Loc) (B : BRec)
    (k : List w8) (cl : Loc) (Bc : BRec) (v : List w8) (hB : T.bs !! bl = some B)
    (hfr : T.bs !! cl = none) (hent : entryIn W B k v) (h16 : 16 ≤ v.length)
    (hcib : Bc.ib = ibOf v) (hcbm : Bc.bm = ∅) (hcns : Bc.ns = ∅)
    (hkeys : inBucketRoot v ≠ 0 → treeKeys W.pages (inBucketRoot v) none none)
    (htoks : bktToks (GF := GF) γ W B ⊢ bktToks γ W (bOpen B k cl) ∗ bktToks γ W Bc) :
    txShape (GF := GF) γ W T ⊢ txShape γ W (wtxAdd T st bl (bOpen B k cl) cl Bc) := by
  have hne : cl ≠ bl := by intro e; rw [e, hB] at hfr; cases hfr
  have hfr' : (<[bl := bOpen B k cl]> T.bs) !! cl = none := by
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hfr
  have hbs : (wtxAdd T st bl (bOpen B k cl) cl Bc).bs = <[cl := Bc]> (<[bl := bOpen B k cl]> T.bs) :=
    rfl
  have Hfacts := txFacts_add W T st bl B k cl Bc v hB hfr hent h16 hcib hcbm hcns hkeys
  unfold txShape
  rw [hbs]
  iintro ⟨%M, Ha, %Hd, Hbs, %Hf⟩
  iexists M
  iframe Ha
  isplitr
  · ipureintro; exact Hd
  isplitl [Hbs]
  · icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)
      (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hrest⟩
    icases htoks $$ Hb with ⟨Hb, Hc⟩
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)
      (show Std.get? (<[bl := bOpen B k cl]> T.bs) cl = none from hfr')).2
    iframe Hc
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)).2
    iframe
  · ipureintro
    have := Hfacts Hf
    rw [hbs] at this
    exact this

/-- The transaction's shape with the bucket `bl`'s record unchanged. -/
theorem txShape_same (γ : GName) (W : WView) (T T' : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) (hT' : T'.bs = <[bl := B]> T.bs) :
    txShape (GF := GF) γ W T ⊢ txShape γ W T' := by
  have h : T'.bs = T.bs := by rw [hT', GMap.insert_id _ _ _ hB]
  unfold txShape
  rw [h]
  have hn : ∀ C, bktNested W T' C ↔ bktNested W T C := by
    intro C; unfold bktNested; rw [h]
  simp only [hn]
  exact .rfl

end txadd2

/-! ### Where a seek's result is -/

section seek
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

theorem ownHas_snoc (pages : GMap Nat (List w8)) (c p : Nat) (h : ownHas pages c p) (pg : List w8)
    (hpg : pages !! p = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) (pg' : List w8) (hpg' : pages !! branchPgid pg i = some pg') :
    ownHas pages c (branchPgid pg i) := by
  induction h with
  | root r pg0 hpg0 => exact ownHas.child r pg i _ hpg hb hi (ownHas.root _ pg' hpg')
  | child r pg0 j id hpg0 hb0 hj _ ih => exact ownHas.child r pg0 j _ hpg0 hb0 hj (ih hpg)

theorem w64_nat (x : w64) : W64 ((uint.nat x : Nat) : Int) = x := by
  unfold uint.nat; word

theorem uint_nat_lt (x : w64) : uint.nat x < 2 ^ 64 := by
  unfold uint.nat; word

/-- A position reached from the root: a node, or a page under one of the bucket's page
positions (`posRoot`), reached from it through branches. -/
def posReach (W : WView) (B : BRec) (pid : w64) : Prop :=
  resolve B pid = none → B.ib.root' ≠ W64 0 → ∃ c, posRoot B c ∧ ownHas W.pages c (uint.nat pid)

theorem posReach_root (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B) :
    posReach W B B.ib.root' := by
  intro hres hr
  unfold resolve at hres; rw [if_neg hr] at hres
  have hrn : B.bv.rootNode' = null := by
    by_cases h : B.bv.rootNode' = null
    · exact h
    · rw [hc.2.2.2.1 h] at hres; cases hres
  obtain ⟨_, ht⟩ := hc.2.1 hr
  have ht' := ht hrn
  cases ht' with
  | page _ pg _ hpg _ _ => exact ⟨_, Or.inl ⟨hrn, hr, rfl⟩, ownHas.root _ pg hpg⟩

/-- The last element of a path of a clean bucket is a leaf position reached from the root. -/
theorem wpath_reach (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → posOK W hwm B pid → posReach W B pid →
    ∃ pid' r ks, es.getLast? = some r ∧ refAt W B pid' r ∧ posOK W hwm B pid' ∧
      posReach W B pid' ∧ kidsAt W B pid' = some (true, ks) := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [wpath])
  | cons r rs ih =>
    intro pid h hpos hreach
    cases rs with
    | nil =>
      obtain ⟨hr, -, ks, hk⟩ := h
      exact ⟨pid, r, ks, rfl, hr, hpos, hreach, hk⟩
    | cons r2 rs' =>
      obtain ⟨hr, hi, ks, c, hk, hc', hrest⟩ := h
      have hcpos : posOK W hwm B c ∧ posReach W B c := by
        unfold kidsAt at hk
        rcases hpos.2 with ⟨l, rr, hres, hrr⟩ | ⟨hres, hpg⟩
        · rw [hres] at hk
          simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hleaf, rfl⟩ := hk
          simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.getElem?_map] at hc'
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hc'
          have hpc := posOK_node_child W hwm bl B l rr hc hrr hleaf _ w hw
          refine ⟨hpc, fun hres' hr0 => ?_⟩
          have hnm : B.nm !! w.pgid = none := by
            unfold resolve at hres'; rw [if_neg hr0] at hres'; exact hres'
          obtain ⟨pg, hpg, -⟩ := posOK_page W hwm B w.pgid hr0 hres' hpc
          have hres0 : resolve B pid = some l := hres
          have hl : B.ns !! l = some rr := hrr
          refine ⟨uint.nat w.pgid, Or.inr ⟨l, (sint.Z r.index').toNat,
            ⟨rr, w, hl, hleaf, hw, (w64_nat w.pgid).symm, by rw [w64_nat]; exact hnm⟩,
            uint_nat_lt _⟩, ownHas.root _ pg hpg⟩
        · rw [hres] at hk
          rcases hpg with ⟨h0, -, -, -, hinl⟩ | ⟨hr0, hwf, hfree⟩
          · have hp0 := hpos.1 h0
            simp only [wpageAt, h0, hp0, ↓reduceIte, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hk
            obtain ⟨hleaf, -⟩ := hk
            exfalso; revert hleaf; simp [hinl.2.1]
          · obtain ⟨pg, hpg, hpa, -, -⟩ := posOK_page W hwm B pid hr0 hres hpos
            simp only [hpa, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
            obtain ⟨hleaf, rfl⟩ := hk
            obtain ⟨-, -, -, hkind⟩ := treeWF_page _ _ _ pg hwf hpg
            rcases hkind with ⟨hfl, -⟩ | ⟨hfl, -, hkids⟩
            · exfalso; revert hleaf; simp [hfl]
            · rw [if_neg (by rw [hfl]; unfold branchPageFlag leafPageFlag; decide),
                List.getElem?_map] at hc'
              obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.1 hc'
              have hil := (List.mem_range.1 (List.mem_of_getElem? hi'))
              refine ⟨posOK_page_child W hwm B pid pg hr0 hpg hfl hkids hfree _ hil, fun _ _ => ?_⟩
              obtain ⟨c0, hpr, hown⟩ := hreach hres hr0
              rw [uint_nat_W64_w _ (branchPgid_lt pg i)]
              cases hkids i hil with
              | page _ pg' _ hpg' _ _ =>
                exact ⟨c0, hpr, ownHas_snoc _ _ _ hown pg hpg hfl i hil pg' hpg'⟩
      obtain ⟨pid', r', ks', hl, h1, h2, h3, h4⟩ := ih c hrest hcpos.1 hcpos.2
      exact ⟨pid', r', ks', by simpa using hl, h1, h2, h3, h4⟩

/-- Where a seek's result (key, value, flags) is, the key's bytes `kbs` and the value's `vbs`:
nil, an entry of a leaf node of the bucket, or an element of a leaf page of the bucket (its
inline page, or a page reached from one of its page positions). -/
def seekRes0 (W : WView) (hwm : Nat) (B : BRec) (kv : GoSlice × GoSlice × w32)
    (kbs vbs : List w8) : Prop :=
  (kv = (slice.nil, slice.nil, W32 0) ∧ kbs = []) ∨
  (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry), B.ns !! l = some r ∧
    r.nv.isLeaf' = true ∧ r.ins[i]? = some it ∧ r.ws[i]? = some w ∧
    kv = (it.key', it.value', it.flags') ∧ w.key = kbs ∧ w.value = vbs) ∨
  (∃ (pid : w64) (p : Loc) (pg : List w8) (i : Nat), wpageAt W B pid = some (p, pg) ∧
    (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale ∧ inlineOK pg) ∧
    (B.ib.root' ≠ W64 0 → W.pages !! uint.nat pid = some pg ∧ treeWF W.pages hwm (uint.nat pid) ∧
      ∃ c, posRoot B c ∧ ownHas W.pages c (uint.nat pid)) ∧
    16 ≤ pg.length ∧ leafWF pg pg.length ∧ pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
    kv = kvResult p pg (i : Int) ∧ leafKey pg i = kbs ∧ leafValue pg i = vbs)

/-- `seekRes0`, and a node entry's inode has the entry's flags. -/
def seekRes (W : WView) (hwm : Nat) (B : BRec) (kv : GoSlice × GoSlice × w32)
    (kbs vbs : List w8) : Prop :=
  (kv = (slice.nil, slice.nil, W32 0) ∧ kbs = []) ∨
  (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry), B.ns !! l = some r ∧
    r.nv.isLeaf' = true ∧ r.ins[i]? = some it ∧ r.ws[i]? = some w ∧
    kv = (it.key', it.value', it.flags') ∧ w.key = kbs ∧ w.value = vbs ∧ it.flags' = w.flags) ∨
  (∃ (pid : w64) (p : Loc) (pg : List w8) (i : Nat), wpageAt W B pid = some (p, pg) ∧
    (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale ∧ inlineOK pg) ∧
    (B.ib.root' ≠ W64 0 → W.pages !! uint.nat pid = some pg ∧ treeWF W.pages hwm (uint.nat pid) ∧
      ∃ c, posRoot B c ∧ ownHas W.pages c (uint.nat pid)) ∧
    16 ≤ pg.length ∧ leafWF pg pg.length ∧ pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
    kv = kvResult p pg (i : Int) ∧ leafKey pg i = kbs ∧ leafValue pg i = vbs)

theorem wpageAt_inj (W : WView) (hvw : viewOK W) (B : BRec) (a b : w64) (p : Loc)
    (pg pg' : List w8) (ha : wpageAt W B a = some (p, pg)) (hb : wpageAt W B b = some (p, pg')) :
    pg = pg' ∧ (B.ib.root' ≠ W64 0 → a = b) := by
  unfold wpageAt at ha hb
  by_cases hr : B.ib.root' = W64 0
  · rw [if_pos hr] at ha hb
    split at ha <;> split at hb <;> simp_all
  · rw [if_neg hr] at ha hb
    obtain ⟨pa, hpa, ea⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨pb, hpb, eb⟩ := Option.map_eq_some_iff.1 hb
    simp only [Prod.mk.injEq] at ea eb
    obtain ⟨ea1, rfl⟩ := ea
    obtain ⟨eb1, rfl⟩ := eb
    have h1 := loc_add_inj W.data (ea1.trans eb1.symm)
    have h2 : uint.nat a * W.ps = uint.nat b * W.ps := by exact_mod_cast h1
    have hps : 0 < W.ps := by have := hvw.2.1; omega
    have h3 : uint.nat a = uint.nat b := Nat.eq_of_mul_eq_mul_right hps h2
    have hab : a = b := by
      have := congrArg (fun n : Nat => W64 (n : Int)) h3
      simpa [w64_nat] using this
    subst hab
    rw [hpa] at hpb; cases hpb
    exact ⟨rfl, fun _ => rfl⟩

theorem kvResult_nat (p : Loc) (pg : List w8) (i : Int)
    (h : ¬ (pageCount pg = 0 ∨ (pageCount pg : Int) ≤ i)) :
    kvResult p pg i = kvResult p pg (i.toNat : Int) := by
  unfold kvResult
  rw [if_neg h, if_neg (by omega)]
  simp only [Int.toNat_natCast]

/-- Where a seek's result is (`Cursor.seek.sspec`'s `seekAt`, the path's last element reached
from the root). -/
theorem seek_res0 (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hvw : viewOK W) (path : List elemRef) (kv : GoSlice × GoSlice × w32)
    (hp : wpath W B B.ib.root' path) (hs : seekAt W B path kv) :
    ∃ kbs vbs, seekRes0 W hwm B kv kbs vbs := by
  obtain ⟨pid', r, ks, hl, href, hpos, hreach, hk⟩ :=
    wpath_reach W hwm bl B hc path _ hp (posOK_root W hwm bl B hc) (posReach_root W hwm bl B hc)
  obtain ⟨e, he, hcase⟩ := hs
  rw [hl] at he; cases he
  rcases hcase with ⟨hnn, rr, hrr, hkv⟩ | ⟨hnull, pid, pg, hpa, hkv⟩
  · rcases href with ⟨l, hres, hnode, -⟩ | ⟨-, hn, -⟩
    · rw [hnode] at hrr
      have hleaf : rr.nv.isLeaf' = true := by
        unfold kidsAt at hk; rw [hres] at hk
        simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        exact hk.1
      have hlen : rr.ins.length = rr.ws.length := (hc.2.2.2.2.2.2.2.1 l rr hrr).2.1
      unfold nodeKV at hkv
      split at hkv
      · exact ⟨[], [], Or.inl ⟨hkv, rfl⟩⟩
      · cases hit : rr.ins[(sint.Z r.index').toNat]? with
        | none => rw [hit] at hkv; exact ⟨[], [], Or.inl ⟨hkv, rfl⟩⟩
        | some it =>
          rw [hit] at hkv
          have hil := (List.getElem?_eq_some_iff.1 hit).1
          obtain ⟨w, hw⟩ : ∃ w, rr.ws[(sint.Z r.index').toNat]? = some w :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          exact ⟨w.key, w.value, Or.inr (Or.inl ⟨l, rr, _, it, w, hrr, hleaf, hit, hw, hkv, rfl, rfl⟩)⟩
    · exact absurd hn hnn
  · rcases href with ⟨l, hres, hnode, -⟩ | ⟨hres, -, pg', hpa'⟩
    · exfalso
      rw [hnull] at hnode
      unfold resolve at hres
      split at hres
      · split at hres
        · cases hres
        · rename_i hne; cases hres; exact hne hnode.symm
      · exact (hc.2.2.2.2.1 _ _ hres).1 hnode.symm
    · obtain ⟨rfl, hpid⟩ := wpageAt_inj W hvw B pid pid' _ _ _ hpa hpa'
      have hleaf : pageFlags pg = leafPageFlag := by
        unfold kidsAt at hk; rw [hres, hpa'] at hk
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        exact of_decide_eq_true hk.1
      -- the page's facts
      have hfacts : 16 ≤ pg.length ∧ leafWF pg pg.length ∧
          (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale ∧ inlineOK pg) ∧
          (B.ib.root' ≠ W64 0 → W.pages !! uint.nat pid' = some pg ∧
            treeWF W.pages hwm (uint.nat pid') ∧
            ∃ c, posRoot B c ∧ ownHas W.pages c (uint.nat pid')) := by
        by_cases hr0 : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hres; rw [if_pos hr0] at hres
            split at hres
            · assumption
            · cases hres
          obtain ⟨h1, h2, h3⟩ := hc.1 hr0 hrn
          have hpg : pg = B.ipg := by
            unfold wpageAt at hpa'; rw [if_pos hr0] at hpa'
            split at hpa'
            · simp only [Option.some.injEq, Prod.mk.injEq] at hpa'; exact hpa'.2.symm
            · cases hpa'
          subst hpg
          refine ⟨h3.2.2.2.1, h3.2.2.1, fun _ => ⟨h1, ?_, h3⟩, fun h => absurd hr0 h⟩
          rcases h2 with h | h <;> rw [h] <;> nofun
        · obtain ⟨pg0, hpg0, hpa0, hwf, -⟩ := posOK_page W hwm B pid' hr0 hres hpos
          rw [hpa0] at hpa'
          simp only [Option.some.injEq, Prod.mk.injEq] at hpa'
          obtain ⟨-, rfl⟩ := hpa'
          obtain ⟨h16, -, -, hk2⟩ := treeWF_page _ _ _ _ hwf hpg0
          have hlw : leafWF pg0 pg0.length := by
            rcases hk2 with ⟨-, h, -⟩ | ⟨hb, -⟩
            · exact h
            · rw [hb] at hleaf; exact absurd hleaf (by unfold branchPageFlag leafPageFlag; decide)
          exact ⟨h16, hlw, fun h => absurd h hr0, fun _ => ⟨hpg0, hwf, hreach hres hr0⟩⟩
      obtain ⟨h16, hlw, hinl, htree⟩ := hfacts
      by_cases hc0 : pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z r.index'
      · refine ⟨[], [], Or.inl ⟨?_, rfl⟩⟩
        rw [hkv]; unfold kvResult; rw [if_pos hc0]
      · have hi : (sint.Z r.index').toNat < pageCount pg := by omega
        refine ⟨_, _, Or.inr (Or.inr ⟨pid', r.page', pg, (sint.Z r.index').toNat, hpa', hinl,
          htree, h16, hlw, hleaf, hi, ?_, rfl, rfl⟩)⟩
        rw [hkv, kvResult_nat _ _ _ hc0]

/-- `seek_res0`, the key's bytes `kbs` (`seekKey`). -/
theorem seek_res0k (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hvw : viewOK W) (path : List elemRef) (kv : GoSlice × GoSlice × w32)
    (hp : wpath W B B.ib.root' path) (hs : seekAt W B path kv) (kbs : List w8)
    (hkey : seekKey W B path kbs) :
    kv = (slice.nil, slice.nil, W32 0) ∨ ∃ vbs, seekRes0 W hwm B kv kbs vbs := by
  obtain ⟨pid', r, ks, hl, href, hpos, hreach, hk⟩ :=
    wpath_reach W hwm bl B hc path _ hp (posOK_root W hwm bl B hc) (posReach_root W hwm bl B hc)
  obtain ⟨e, he, hcase⟩ := hs
  rw [hl] at he; cases he
  rcases hcase with ⟨hnn, rr, hrr, hkv⟩ | ⟨hnull, pid, pg, hpa, hkv⟩
  · rcases href with ⟨l, hres, hnode, -⟩ | ⟨-, hn, -⟩
    · have hrr0 := hrr
      rw [hnode] at hrr
      have hleaf : rr.nv.isLeaf' = true := by
        unfold kidsAt at hk; rw [hres] at hk
        simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        exact hk.1
      have hlen : rr.ins.length = rr.ws.length := (hc.2.2.2.2.2.2.2.1 l rr hrr).2.1
      unfold nodeKV at hkv
      split at hkv
      · exact Or.inl hkv
      · rename_i hcond
        cases hit : rr.ins[(sint.Z r.index').toNat]? with
        | none => rw [hit] at hkv; exact Or.inl hkv
        | some it =>
          rw [hit] at hkv
          have hil := (List.getElem?_eq_some_iff.1 hit).1
          obtain ⟨w, hw⟩ : ∃ w, rr.ws[(sint.Z r.index').toNat]? = some w :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          exact Or.inr ⟨w.value, Or.inr (Or.inl ⟨l, rr, _, it, w, hrr, hleaf, hit, hw, hkv,
            (hkey r hl).1 rr w hnn hrr0 hw hcond, rfl⟩)⟩
    · exact absurd hn hnn
  · rcases href with ⟨l, hres, hnode, -⟩ | ⟨hres, -, pg', hpa'⟩
    · exfalso
      rw [hnull] at hnode
      unfold resolve at hres
      split at hres
      · split at hres
        · cases hres
        · rename_i hne; cases hres; exact hne hnode.symm
      · exact (hc.2.2.2.2.1 _ _ hres).1 hnode.symm
    · obtain ⟨rfl, hpid⟩ := wpageAt_inj W hvw B pid pid' _ _ _ hpa hpa'
      have hleaf : pageFlags pg = leafPageFlag := by
        unfold kidsAt at hk; rw [hres, hpa'] at hk
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        exact of_decide_eq_true hk.1
      -- the page's facts
      have hfacts : 16 ≤ pg.length ∧ leafWF pg pg.length ∧
          (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale ∧ inlineOK pg) ∧
          (B.ib.root' ≠ W64 0 → W.pages !! uint.nat pid' = some pg ∧
            treeWF W.pages hwm (uint.nat pid') ∧
            ∃ c, posRoot B c ∧ ownHas W.pages c (uint.nat pid')) := by
        by_cases hr0 : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hres; rw [if_pos hr0] at hres
            split at hres
            · assumption
            · cases hres
          obtain ⟨h1, h2, h3⟩ := hc.1 hr0 hrn
          have hpg : pg = B.ipg := by
            unfold wpageAt at hpa'; rw [if_pos hr0] at hpa'
            split at hpa'
            · simp only [Option.some.injEq, Prod.mk.injEq] at hpa'; exact hpa'.2.symm
            · cases hpa'
          subst hpg
          refine ⟨h3.2.2.2.1, h3.2.2.1, fun _ => ⟨h1, ?_, h3⟩, fun h => absurd hr0 h⟩
          rcases h2 with h | h <;> rw [h] <;> nofun
        · obtain ⟨pg0, hpg0, hpa0, hwf, -⟩ := posOK_page W hwm B pid' hr0 hres hpos
          rw [hpa0] at hpa'
          simp only [Option.some.injEq, Prod.mk.injEq] at hpa'
          obtain ⟨-, rfl⟩ := hpa'
          obtain ⟨h16, -, -, hk2⟩ := treeWF_page _ _ _ _ hwf hpg0
          have hlw : leafWF pg0 pg0.length := by
            rcases hk2 with ⟨-, h, -⟩ | ⟨hb, -⟩
            · exact h
            · rw [hb] at hleaf; exact absurd hleaf (by unfold branchPageFlag leafPageFlag; decide)
          exact ⟨h16, hlw, fun h => absurd h hr0, fun _ => ⟨hpg0, hwf, hreach hres hr0⟩⟩
      obtain ⟨h16, hlw, hinl, htree⟩ := hfacts
      by_cases hc0 : pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z r.index'
      · refine Or.inl ?_
        rw [hkv]; unfold kvResult; rw [if_pos hc0]
      · have hi : (sint.Z r.index').toNat < pageCount pg := by omega
        refine Or.inr ⟨_, Or.inr (Or.inr ⟨pid', r.page', pg, (sint.Z r.index').toNat, hpa', hinl,
          htree, h16, hlw, hleaf, hi, ?_, (hkey r hl).2 hnull pid' pg hpa' hc0, rfl⟩)⟩
        rw [hkv, kvResult_nat _ _ _ hc0]

end seek

section seekown
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The key a seek returned, with its bytes, lent out (and back); a node entry's flags are its
inode's. -/
theorem seekRes_key_acc (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (k v : GoSlice) (f : w32) (kbs vbs : List w8)
    (hc : W.data.locCar ≠ 0) (hcl : bktClean W hwm bl B) (h : seekRes0 W hwm B (k, v, f) kbs vbs) :
    wctx (GF := GF) W bl B txl pmap pm dqp ⊢ ∃ (dq : DFrac), ⌜seekRes W hwm B (k, v, f) kbs vbs⌝ ∗
      k ↦*{dq} kbs ∗ (k ↦*{dq} kbs -∗ wctx W bl B txl pmap pm dqp) := by
  iintro Hctx
  rcases h with ⟨h0, rfl⟩ | ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, rfl, rfl⟩ |
    ⟨pid, p, pg, i, hpa, hinl, htree, hlen, hwf, hfl, hi, he, rfl, rfl⟩
  · have hk : k = slice.nil := congrArg Prod.fst h0
    subst hk
    iexists DFrac.own 1
    isplitr
    · ipureintro; exact Or.inl ⟨h0, rfl⟩
    isplitl []
    · iapply ownSlice_nil
    iintro -; iexact Hctx
  · have hk : k = it.key' := congrArg Prod.fst he
    subst hk
    have hns : w.ks ≠ Src.stale :=
      ((hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.1 w (List.mem_of_getElem? hw)).1
    unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases bktOwn_node_acc W bl B l r hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) hit hw $$ Hents
      with ⟨Hi, Hentsback⟩
    isimp only [wOwn] at Hi
    icases Hi with ⟨%Hfp, Hk, Hvv⟩
    icases srcBorrow W hc W.q it.key' w.ks w.key hns $$ [Hpv Hk] with ⟨%dq, -, Hk, Hkback⟩
    · iframe
    iexists dq
    isplitr
    · ipureintro; exact Or.inr (Or.inl ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, rfl, rfl, Hfp.1⟩)
    iframe Hk
    iintro Hk
    ihave Hk := Hkback $$ Hk
    icases Hk with ⟨Hpv, Hk⟩
    ihave Hents := Hentsback $$ [Hk Hvv]
    · unfold wOwn; iframe; ipureintro; exact Hfp
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l r hr]
    iframe
    unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  · have hb := (hwf.2.2.1 i hi).1
    have hk : (kvResult p pg (i : Int)).1 =
        sliceAt p (elemOff i + leafPos pg i) (leafKsize pg i) := by
      unfold kvResult; rw [if_neg (by omega)]; rfl
    have Hres : seekRes W hwm B (k, v, f) (leafKey pg i) (leafValue pg i) :=
      Or.inr (Or.inr ⟨pid, p, pg, i, hpa, hinl, htree, hlen, hwf, hfl, hi, he, rfl, rfl⟩)
    have hk' : k = (kvResult p pg (i : Int)).1 := congrArg Prod.fst he
    subst hk'
    rw [hk, show leafKey pg i = bytesAt pg (elemOff i + leafPos pg i) (leafKsize pg i) from rfl]
    unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    isimp only [bktOwn] at Hb
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    have Hne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    icases wpageAt_acc W B pid p pg hc hpa (fun h => ⟨(hinl h).1, (hinl h).2.1⟩) Hne $$ [Hpv Hpo]
      with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    icases bytes_slice_acc (hG := hG) p dq pg (elemOff i + leafPos pg i) (leafKsize pg i)
      (by omega) (leAt_lt _ _ 4) Hc $$ Hpg with ⟨Hk, Hkback⟩
    iexists dq
    isplitr
    · ipureintro
      rw [← hk]; exact Hres
    iframe Hk
    iintro Hk
    ihave Hpg := Hkback $$ Hk
    ihave Hpg := Hpgback $$ Hpg
    icases Hpg with ⟨Hpv, Hpo⟩
    unfold bktOwn wView; iframe; iframe #; ipureintro; exact Hlgv

end seekown

/-! ### A nested bucket the seek found -/

section found
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

theorem treeKeys_down (pages : GMap Nat (List w8)) (c p : Nat) (h : ownHas pages c p)
    (lo hi : Option (List w8)) (hk : treeKeys pages c lo hi) :
    ∃ lo' hi', treeKeys pages p lo' hi' := by
  induction h generalizing lo hi with
  | root r pg hpg => exact ⟨lo, hi, hk⟩
  | child r pg i id hpg hb hi' _ ih =>
    cases hk with
    | leaf _ pg' _ _ hpg' hl _ _ =>
      rw [hpg] at hpg'; cases hpg'; rw [hb] at hl
      exact absurd hl (by unfold branchPageFlag leafPageFlag; decide)
    | branch _ pg' _ _ _ hpg' _ _ _ _ hch =>
      rw [hpg] at hpg'; cases hpg'
      exact ih _ _ (hch i hi')

/-- The tree of a nested bucket stored in pages of a leaf page under a page position has the
keys of a bucket's tree. -/
theorem treeKeys_entry (W : WView) (B : BRec) (hk : bktKeys W B) (c p : Nat) (hpos : posRoot B c)
    (hown : ownHas W.pages c p) (pg : List w8) (hpg : W.pages !! p = some pg)
    (hl : pageFlags pg = leafPageFlag) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) (hr : inBucketRoot (leafValue pg i) ≠ 0) :
    treeKeys W.pages (inBucketRoot (leafValue pg i)) none none := by
  obtain ⟨bnd, hk1, -, hk3⟩ := hk
  have hc : ∃ lo hi, treeKeys W.pages c lo hi := by
    rcases hpos with ⟨hrn, hr0, rfl⟩ | ⟨l, j, ⟨r, w, hr', hbr, hw, hpj, hnm⟩, hlt⟩
    · exact ⟨none, none, hk1 hrn hr0⟩
    · obtain ⟨-, -, -, h4, -⟩ := hk3 l r hr'
      obtain ⟨-, kind, hkind⟩ := h4 hbr
      obtain ⟨-, hnone⟩ := hkind j w hw
      rw [hpj] at hnone
      obtain ⟨_, -, -, -, -, ht⟩ := hnone hnm
      rw [uint_nat_W64_w c hlt] at ht
      exact ⟨_, _, ht⟩
  obtain ⟨lo, hi', hc⟩ := hc
  obtain ⟨lo', hi'', hp⟩ := treeKeys_down W.pages c p hown lo hi' hc
  cases hp with
  | leaf _ pg' _ _ hpg' _ _ hnest =>
    rw [hpg] at hpg'; cases hpg'; exact hnest i hi hf hr
  | branch _ pg' _ _ _ hpg' hb _ _ _ _ =>
    rw [hpg] at hpg'; cases hpg'; rw [hb] at hl
    exact absurd hl (by unfold branchPageFlag leafPageFlag; decide)

/-- A nested bucket the seek found (its flags returned): its value good, the bucket's entry
(`entryIn`), its tree's keys, and where its bytes are. -/
theorem seekRes_bkt (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hvw : viewOK W) (hk : bktKeys W B) (k v : GoSlice) (f : w32) (kbs vbs : List w8)
    (h : seekRes W hwm B (k, v, f) kbs vbs) (hf : isBktFlag f) :
    bvalOK W.pages hwm vbs ∧ entryIn W B kbs vbs ∧
    (inBucketRoot vbs ≠ 0 → treeKeys W.pages (inBucketRoot vbs) none none) ∧
    ∃ src : Src, (src = Src.view ∨ src = Src.own DFrac.discard) ∧
      ((src = Src.view ∧ inViewAt W v vbs) ∨ (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode)
        (w : WEntry), B.ns !! l = some r ∧ r.ins[i]? = some it ∧ r.ws[i]? = some w ∧
        it.value' = v ∧ w.value = vbs ∧ w.vs = src)) := by
  rcases h with ⟨h0, -⟩ | ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, hkey, hval, hfl⟩ |
    ⟨pid, p, pg, i, hpa, hinl, htree, hlen, hwf, hflp, hi, he, hkey, hval⟩
  · simp only [Prod.mk.injEq] at h0
    rw [h0.2.2] at hf; exact absurd hf (by unfold isBktFlag; decide)
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    subst hkey hval
    rw [hfl] at hf
    have hmem := List.mem_of_getElem? hw
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := hc.2.2.2.2.2.2.2.1 l r hr
    obtain ⟨hb, hvs⟩ := h11 hleaf w hmem hf
    obtain ⟨bnd, -, -, hk3⟩ := hk
    refine ⟨hb, Or.inl ⟨l, r, w, hr, hleaf, hmem, rfl, hf, rfl⟩,
      fun h0 => (hk3 l r hr).2.2.2.2.2 hleaf w hmem hf h0, w.vs, hvs, Or.inr ⟨l, r, i, it, w, hr, hit, hw, rfl, rfl, rfl⟩⟩
  · unfold kvResult at he
    rw [if_neg (by omega)] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    simp only [Int.toNat_natCast] at hf ⊢
    rw [isBktFlag_iff _ (by unfold leafFlags; exact leAt_lt _ _ 4)] at hf
    subst hkey hval
    by_cases hr : B.ib.root' = W64 0
    · obtain ⟨-, -, hok⟩ := hinl hr
      have := (hok.2.2.2.2 i hi).2
      rw [hf] at this; exact absurd this (by unfold bucketLeafFlag; decide)
    · obtain ⟨hpg, ht, c, hpos, hown⟩ := htree hr
      have hpa' := hpa
      unfold wpageAt at hpa'; rw [if_neg hr, hpg] at hpa'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpa'
      obtain ⟨rfl, -⟩ := hpa'
      obtain ⟨-, -, -, hkd⟩ := treeWF_page _ _ _ _ ht hpg
      rcases hkd with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
      · refine ⟨⟨hbw i hi hf, fun h0 => ((hvw.2.2.2.2.1 _ _ hpg).1 hflp i hi).2 hf h0⟩,
          Or.inr ⟨c, uint.nat pid, pg, i, hpos, hown, hpg, hflp, hi, rfl, hf, rfl⟩,
          fun h0 => treeKeys_entry W B hk c _ hpos hown pg hpg hflp i hi hf h0, Src.view,
          Or.inl rfl, Or.inl ⟨rfl, ?_⟩⟩
        have hb := (hwf.2.2.1 i hi).1
        exact inViewAt_sub W _ _ (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i)
          (inViewLoc_page W _ _ hpg) (by omega) (leAt_lt _ _ 4)
      · rw [hb] at hflp; exact absurd hflp (by unfold branchPageFlag leafPageFlag; decide)

end found

/-! ### The transaction with a bucket added, the new bucket fresh -/

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `ownWriteTx_bkt_add`, the added bucket `cl` not one of the transaction's before. -/
theorem ownWriteTx_bkt_add2 (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗
      ((∀ (st : TxStats) (B' : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ wView W -∗ ownWriteTx W txl (wtxUpd T st bl B')) ∧
      (∀ (st : TxStats) (B' : BRec) (cl : Loc) (Bc : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧
          (∀ n c, B'.bm !! n = some c → c = cl ∨ (T.bs !! c).isSome) ∧
          bktClean W (uint.nat T.mv.pgid') cl Bc ∧ Bc.bv.tx' = txl ∧ Bc.bm = ∅⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ bktOwn W cl Bc -∗ wView W -∗
        ownWriteTx W txl (wtxAdd T st bl B' cl Bc) ∗ ⌜T.bs !! cl = none⌝)) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  isplitr
  · ipureintro; exact Hok
  iframe Hrest Hm Hpm Hb Hv
  isplit
  · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv
    obtain ⟨Hcl, Htx, Hbm⟩ := Hc3
    unfold wtxUpd
    isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
    · iframe
      iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
      iframe
    iframe
    ipureintro
    exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hcl Htx Hbm⟩
  iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv
  obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
  ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
    (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
  · iframe
  isimp only [bktOwn] at Hc
  icases Hc with ⟨Hcbv, Hcrest⟩
  icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
  · iframe
  have Hfr' : T.bs !! cl = none := by
    have hne : cl ≠ bl := by
      intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
  unfold wtxAdd
  isplitl
  · isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
    · iframe
      iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
        (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
      iframe
      unfold bktOwn; iframe
    iframe
    ipureintro
    exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩
  · ipureintro; exact Hfr'

end own

/-! ### Facts out of the transaction and its shape -/

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The transaction's buckets are not at `null`. -/
theorem ownWriteTx_nonnull (W : WView) (txl : Loc) (T : WTx) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜∀ b B, T.bs !! b = some B → b ≠ null⌝ ∗ ownWriteTx W txl T := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  ihave Hbs := (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (Ψ := fun bl B => iprop(bktOwn (GF := GF) W bl B ∗ ⌜bl ≠ null⌝)) (fun {k x} _ => by
      unfold bktOwn
      iintro ⟨Hbv, Hr⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hbv with ⟨Hbv, %h⟩
      iframe; ipureintro; exact h)) $$ Hbs
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hbs with ⟨Hbs, Hnn⟩
  ihave %Hnn := (BigSepM.bigSepM_pure (M := GMap Loc) (φ := fun bl (_ : BRec) => bl ≠ null)).1 $$ Hnn
  isplitr
  · ipureintro; intro b B h; exact Hnn b B h
  iframe; ipureintro; exact Hok

end facts

section sfacts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The facts of the transaction's shape. -/
theorem txShape_facts (γ : GName) (W : WView) (T : WTx) :
    txShape (GF := GF) γ W T ⊢
      ⌜∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B⌝ ∗ txShape γ W T := by
  unfold txShape
  iintro ⟨%M, Ha, %Hd, Hbs, %Hf⟩
  isplitr
  · ipureintro; exact Hf
  iexists M; iframe; ipureintro; exact ⟨Hd, Hf⟩

end sfacts

/-! ### A bucket's shape out of the transaction's, and back changed -/

section upd
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- How a bucket's record may change in place: its root kept, its header too while it has no
root node, its opened buckets kept, its entries kept, its keys a B+tree's. -/
def bktUpdOK (W : WView) (B B'' : BRec) : Prop :=
  B''.ib.root' = B.ib.root' ∧ (B''.bv.rootNode' = null → B.bv.rootNode' = null ∧ B''.ib = B.ib) ∧
  B''.bm = B.bm ∧ (∀ k v, entryIn W B k v → entryIn W B'' k v) ∧ bktKeys W B''

theorem txFacts_upd2 (W : WView) (T T' : WTx) (bl : Loc) (B B'' : BRec)
    (hB : T.bs !! bl = some B) (hT' : T'.bs = <[bl := B'']> T.bs) (hu : bktUpdOK W B B'')
    (hf : ∀ bl B, T.bs !! bl = some B → bktKeys W B ∧ bktNested W T B) :
    ∀ bl' C, T'.bs !! bl' = some C → bktKeys W C ∧ bktNested W T' C := by
  obtain ⟨hroot, hrn, hbm, hent, hk⟩ := hu
  have hlk : ∀ y, T'.bs !! y = if y = bl then some B'' else T.bs !! y := by
    intro y; rw [hT']
    by_cases h : y = bl
    · subst h; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]
  have htgt : ∀ c C0 (v : List w8), T.bs !! c = some C0 → C0.ib.root' = (ibOf v).root' →
      (C0.bv.rootNode' = null → C0.ib = ibOf v) →
      ∃ C', T'.bs !! c = some C' ∧ C'.ib.root' = (ibOf v).root' ∧
        (C'.bv.rootNode' = null → C'.ib = ibOf v) := by
    intro c C0 v h0 h1 h2
    rw [hlk]
    by_cases hc : c = bl
    · subst hc; rw [hB] at h0; cases h0
      refine ⟨B'', by rw [if_pos rfl], by rw [hroot]; exact h1, fun h => ?_⟩
      obtain ⟨h3, h4⟩ := hrn h
      rw [h4]; exact h2 h3
    · exact ⟨C0, by rw [if_neg hc]; exact h0, h1, h2⟩
  have hnest : ∀ C C2, (∀ k c, C2.bm !! k = some c → C.bm !! k = some c) →
      (∀ k v, entryIn W C k v → entryIn W C2 k v) → bktNested W T C → bktNested W T' C2 := by
    intro C C2 hm he hn k c hkc
    obtain ⟨C0, v, h0, h1, h2, h3, h4⟩ := hn k c (hm k c hkc)
    obtain ⟨C', h5, h6, h7⟩ := htgt c C0 v h0 h3 h4
    exact ⟨C', v, h5, he k v h1, h2, h6, h7⟩
  intro bl' C hC
  rw [hlk] at hC
  by_cases h : bl' = bl
  · rw [if_pos h] at hC; cases hC
    exact ⟨hk, hnest B B'' (fun k c h => by rw [← hbm]; exact h) hent (hf bl B hB).2⟩
  · rw [if_neg h] at hC
    exact ⟨(hf bl' C hC).1, hnest C C (fun _ _ h => h) (fun _ _ h => h) (hf bl' C hC).2⟩

end upd

section updown
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The shape of the bucket `bl` out of the transaction's, and back, the bucket's record changed
(`bktUpdOK`). -/
theorem txShape_acc (γ : GName) (W : WView) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    txShape (GF := GF) γ W T ⊢ bktShape γ W B ∗
      (∀ (T' : WTx) (B'' : BRec), ⌜T'.bs = <[bl := B'']> T.bs ∧ bktUpdOK W B B''⌝ -∗
        bktToks γ W B'' -∗ txShape γ W T') := by
  unfold txShape
  iintro ⟨%M, Ha, %Hd, Hbs, %Hf⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hrest⟩
  isplitl [Hb]
  · unfold bktShape; iframe Hb; ipureintro; exact (Hf bl B hB).1
  iintro %T' %B'' %Hc Hb''
  obtain ⟨hT', hu⟩ := Hc
  iexists M
  iframe Ha
  isplitr
  · ipureintro; exact Hd
  isplitl
  · rw [hT']
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun _ B => bktToks (GF := GF) γ W B)).2
    iframe
  · ipureintro; exact txFacts_upd2 W T T' bl B B'' hB hT' hu Hf

end updown

section noderes
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- `b.node(root, nil)` of a bucket without a root node gives it one. -/
theorem nodeRes_root_ne (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hrn : B.bv.rootNode' = null) (p : Loc) (pg : List w8) (src : Src) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats) (h : nodeRes B bl B.ib.root' null p pg src l B' st st') :
    B'.bv.rootNode' ≠ null := by
  rcases h with ⟨hk, -, -⟩ | ⟨-, -, hl, -, s, cs', src', -, -, rfl⟩
  · rw [(hc.2.2.1 hrn).2, GMap.lookup_empty] at hk; cases hk
  · simpa [nodeAdded] using hl

end noderes

section tokib
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A bucket's tokens do not depend on its header but for its root. -/
theorem bktToks_ib (γ : GName) (W : WView) (B : BRec) (ib : internal.common.InBucket)
    (h : ib.root' = B.ib.root') :
    bktToks (GF := GF) γ W { B with ib := ib } ⊣⊢ bktToks γ W B := by
  unfold bktToks
  rw [show ({ B with ib := ib } : BRec).ib.root' = B.ib.root' from h]
  exact .rfl

end tokib

/-! ### The transaction with a bucket added, from `ownWriteTx_put_acc` -/

section own2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `ownWriteTx_put_add`, the added bucket `cl` not one of the transaction's before. -/
theorem ownWriteTx_put_add2 (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗ rootHalf txl bl ∗
      ((∀ (st : TxStats) (B' : BRec),
          ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
          TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
          T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ wView W -∗ rootHalf txl bl -∗
          ownWriteTx W txl (wtxUpd T st bl B')) ∧
        (∀ (st : TxStats) (B' : BRec) (cl : Loc) (Bc : BRec),
          ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧
            (∀ n c, B'.bm !! n = some c → c = cl ∨ (T.bs !! c).isSome) ∧
            bktClean W (uint.nat T.mv.pgid') cl Bc ∧ Bc.bv.tx' = txl ∧ Bc.bm = ∅⌝ -∗
          TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
          T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ bktOwn W cl Bc -∗ wView W -∗ rootHalf txl bl -∗
          ownWriteTx W txl (wtxAdd T st bl B' cl Bc) ∗ ⌜T.bs !! cl = none⌝)) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  isplitr
  · ipureintro; exact Hok
  iframe Hrest Hm Hpm Hb Hv
  by_cases hrl : bl = structFieldRef Tx go!"root" txl
  · isplitl []
    · unfold rootHalf; ileft; ipureintro; exact hrl
    isplit
    · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv -
      obtain ⟨Hc, Htx, Hbm⟩ := Hc3
      unfold wtxUpd
      isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
      · iframe
        iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
        iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩
    · iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv -
      obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
      ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
        (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
      · iframe
      isimp only [bktOwn] at Hc
      icases Hc with ⟨Hcbv, Hcrest⟩
      icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
      · iframe
      have Hfr' : T.bs !! cl = none := by
        have hne : cl ≠ bl := by
          intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
      unfold wtxAdd
      isplitl
      rotate_left
      · ipureintro; exact Hfr'
      isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
      · iframe
        iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
          (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
        iframe
        unfold bktOwn; iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩

  · obtain ⟨Br, hBr⟩ := Option.isSome_iff_exists.1 Hok.2.2.2.2.2.2.2.1
    have hBr' : Std.get? (Std.delete T.bs bl) (structFieldRef Tx go!"root" txl) = some Br := by
      show (GMap.delete bl T.bs) !! (structFieldRef Tx go!"root" txl) = some Br
      rw [GMap.lookup_delete_ne _ hrl]; exact hBr
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      hBr').1 $$ Hbs with ⟨Hr, Hrback⟩
    isimp only [bktOwn] at Hr
    icases Hr with ⟨Hrbv, Hr2, Hr3, Hr4, Hr5, Hr6⟩
    icases (wpt_split' _ _ halfQ halfQ 1 one_halves).1 $$ Hrbv with ⟨Hrb1, Hrb2⟩
    isplitl [Hrb1]
    · unfold rootHalf; iright; iexists Br.bv; iframe; ipureintro; exact hrl
    isplit
    · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv Hrh
      obtain ⟨Hc, Htx, Hbm⟩ := Hc3
      unfold rootHalf
      icases Hrh with (%h | ⟨%rv, -, Hrb1⟩)
      · exact absurd h hrl
      icombine Hrb1 Hrb2 gives %Heq
      subst Heq
      ihave Hrbv := (wpt_split' _ _ halfQ halfQ 1 one_halves).2 $$ [Hrb1 Hrb2]
      · iframe
      ihave Hbs := Hrback $$ [Hrbv Hr2 Hr3 Hr4 Hr5 Hr6]
      · unfold bktOwn; iframe
      unfold wtxUpd
      isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
      · iframe
        iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
        iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩
    · iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv Hrh
      obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
      unfold rootHalf
      icases Hrh with (%h | ⟨%rv, -, Hrb1⟩)
      · exact absurd h hrl
      icombine Hrb1 Hrb2 gives %Heq
      subst Heq
      ihave Hrbv := (wpt_split' _ _ halfQ halfQ 1 one_halves).2 $$ [Hrb1 Hrb2]
      · iframe
      ihave Hbs := Hrback $$ [Hrbv Hr2 Hr3 Hr4 Hr5 Hr6]
      · unfold bktOwn; iframe
      ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
        (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
      · iframe
      isimp only [bktOwn] at Hc
      icases Hc with ⟨Hcbv, Hcrest⟩
      icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
      · iframe
      have Hfr' : T.bs !! cl = none := by
        have hne : cl ≠ bl := by
          intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
      unfold wtxAdd
      isplitl
      rotate_left
      · ipureintro; exact Hfr'
      isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
      · iframe
        iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
          (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
        iframe
        unfold bktOwn; iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩

end own2

/-! ### A seek's node entry: its inode's flags -/

section seekfl
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `seekRes0` is `seekRes`: a node entry's inode has its flags (the node's ownership). -/
theorem seekRes_flags (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (kv : GoSlice × GoSlice × w32) (kbs vbs : List w8)
    (h : seekRes0 W hwm B kv kbs vbs) :
    wctx (GF := GF) W bl B txl pmap pm dqp ⊢ ⌜seekRes W hwm B kv kbs vbs⌝ ∗
      wctx W bl B txl pmap pm dqp := by
  iintro Hctx
  rcases h with h | ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, hk, hv⟩ | h
  · isplitr
    · ipureintro; exact Or.inl h
    iexact Hctx
  · unfold wctx
    icases Hctx with ⟨Hb, Hrest⟩
    icases bktOwn_node_acc W bl B l r hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases wOwn_flags_at W r.ins r.ws i $$ Hents with ⟨%Hfl, Hents⟩
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l r hr]
    isplitr
    · ipureintro; exact Or.inr (Or.inl ⟨l, r, i, it, w, hr, hleaf, hit, hw, he, hk, hv, Hfl it w hit hw⟩)
    iframe
  · isplitr
    · ipureintro; exact Or.inr (Or.inr h)
    iexact Hctx

end seekfl

/-! ### A leaf's entries changed (an entry put, nested buckets' entries kept) -/

section leafop
variable [ext : FfiSyntax]

theorem ns_insert_lookup (B : BRec) (l : Loc) (r' : NRec) (y : Loc) :
    (<[l := r']> B.ns) !! y = if y = l then some r' else B.ns !! y := by
  by_cases h : y = l
  · subst h; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), if_neg h]

theorem leaf_not_parent (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (l : Loc) (r : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hp : ry.nv.parent' ≠ null) :
    ry.nv.parent' ≠ l := by
  intro h
  obtain ⟨rp, hrp, hl, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
  rw [h, hr] at hrp; cases hrp; rw [hleaf] at hl; cases hl

/-- The leaf's entries `A ++ D ++ C` replaced by `A ++ E ++ C`, `E`'s keys inside its bounds and
`E` no nested bucket stored in pages: the keys stay a B+tree's. -/
theorem bktKeysB_leafOp2 (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hk : bktKeysB W B bnd)
    (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, keyIn (bnd l).1 (bnd l).2 w.key ∧ (isBktFlag w.flags → inBucketRoot w.value = 0))
    (e1 : r'.nv.isLeaf' = true) (e2 : r'.nv.parent' = r.nv.parent') (e3 : r'.nv.pgid' = r.nv.pgid')
    (e4 : r'.nv.key' = r.nv.key') (e5 : r'.key = r.key)
    (hne : r'.nv.unbalanced' = false → 0 < r'.ws.length) :
    bktKeysB W { B with ns := <[l := r']> B.ns } bnd := by
  obtain ⟨hk1, hkr, hk2⟩ := hk
  have hmem : ∀ w ∈ r'.ws, w ∈ r.ws ∨ w ∈ E := by
    intro w hw
    rw [hws'] at hw; rw [hws]
    simp only [List.mem_append] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hnl := leaf_not_parent W hwm bl B hc l r hr hleaf
  refine ⟨hk1, ?_, ?_⟩
  · intro r0 h0
    show r0.nv.parent' = null
    simp only at h0
    rw [ns_insert_lookup] at h0
    by_cases h : B.bv.rootNode' = l
    · rw [if_pos h] at h0; cases h0; rw [e2]; exact hkr r (by rw [h]; exact hr)
    · rw [if_neg h] at h0; exact hkr r0 h0
  intro y ry hy
  simp only at hy
  rw [ns_insert_lookup] at hy
  by_cases hyl : y = l
  · rw [if_pos hyl] at hy; cases hy; subst hyl
    obtain ⟨c1, c2, c3, -, -, c6⟩ := hk2 y r hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases hmem w hw with h | h
      · exact c1 w h
      · exact (hE w h).1
    · rw [e2]; exact c2
    · intro hp
      rw [e2] at hp
      obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp
      have hpl : r.nv.parent' ≠ y := hnl y r hr hp
      refine ⟨by rw [e4]; exact hkey, rp, i, w, ?_, hw, by rw [hpg, e3], by rw [hwk, e5], by rw [e2]; exact hb⟩
      show (<[y := r']> B.ns) !! r'.nv.parent' = _
      rw [e2, ns_insert_lookup, if_neg hpl]; exact hrp
    · intro h; rw [e1] at h; cases h
    · intro _ hu _; exact hne hu
    · intro _ w hw hb
      rcases hmem w hw with h | h
      · exact c6 hleaf w h hb
      · exact fun h0 => absurd ((hE w h).2 hb) h0
  · rw [if_neg hyl] at hy
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hk2 y ry hy
    refine ⟨c1, c2, ?_, ?_, c5, c6⟩
    · intro hp
      obtain ⟨hkey, rp, i, w, hrp, hw, hpg, hwk, hb⟩ := c3 hp
      have hpl : ry.nv.parent' ≠ l := hnl y ry hy hp
      refine ⟨hkey, rp, i, w, ?_, hw, hpg, hwk, hb⟩
      show (<[l := r']> B.ns) !! ry.nv.parent' = _
      rw [ns_insert_lookup, if_neg hpl]; exact hrp
    · intro hb
      obtain ⟨h2, kind, hkind⟩ := c4 hb
      refine ⟨h2, kind, fun i w hw => ⟨?_, (hkind i w hw).2⟩⟩
      intro l' hl'
      obtain ⟨r0, h0, hk0⟩ := (hkind i w hw).1 l' hl'
      show ∃ r'', (<[l := r']> B.ns) !! l' = some r'' ∧ _
      rw [ns_insert_lookup]
      by_cases h : l' = l
      · subst h; rw [hr] at h0; cases h0
        exact ⟨r', by rw [if_pos rfl], by rw [e1, ← hk0, hleaf]⟩
      · exact ⟨r0, by rw [if_neg h]; exact h0, hk0⟩

theorem posRoot_leafOp (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (c : Nat) :
    posRoot { B with ns := <[l := r']> B.ns } c ↔ posRoot B c := by
  have hpos : ∀ x i c, pagePosAt { B with ns := <[l := r']> B.ns } x i c ↔ pagePosAt B x i c := by
    intro x i c
    unfold pagePosAt
    constructor
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      simp only at hy
      rw [ns_insert_lookup] at hy
      by_cases h : x = l
      · rw [if_pos h] at hy; cases hy; rw [e1] at hl; cases hl
      · rw [if_neg h] at hy; exact ⟨ry, w, hy, hl, hw, hp, hn⟩
    · rintro ⟨ry, w, hy, hl, hw, hp, hn⟩
      have hx : x ≠ l := by
        intro h; subst h; rw [hr] at hy; cases hy; rw [hleaf] at hl; cases hl
      exact ⟨ry, w, by show (<[l := r']> B.ns) !! x = _; rw [ns_insert_lookup, if_neg hx]; exact hy,
        hl, hw, hp, hn⟩
  unfold posRoot
  simp only [hpos]

theorem entryIn_leafOp (W : WView) (B : BRec) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hD : ∀ w ∈ D, ¬ isBktFlag w.flags) (k v : List w8) (h : entryIn W B k v) :
    entryIn W { B with ns := <[l := r']> B.ns } k v := by
  rcases h with ⟨y, ry, w, hy, hl, hw, hk, hb, hv⟩ | ⟨c, p, pg, i, hc, hrest⟩
  · left
    by_cases hyl : y = l
    · subst hyl; rw [hr] at hy; cases hy
      have hw' : w ∈ r'.ws := by
        rw [hws] at hw; rw [hws']
        simp only [List.mem_append] at hw ⊢
        rcases hw with (h | h) | h
        · exact Or.inl (Or.inl h)
        · exact absurd hb (hD w h)
        · exact Or.inr h
      exact ⟨y, r', w, by show (<[y := r']> B.ns) !! y = _; rw [GMap.lookup_insert], e1, hw', hk, hb, hv⟩
    · exact ⟨y, ry, w, by show (<[l := r']> B.ns) !! y = _; rw [ns_insert_lookup, if_neg hyl]; exact hy,
        hl, hw, hk, hb, hv⟩
  · right
    exact ⟨c, p, pg, i, (posRoot_leafOp B l r r' hr hleaf e1 c).2 hc, hrest⟩

theorem putList_split {α : Type} (l : List α) (i : Nat) (ex : Bool) (x : α)
    (hi : ex = true → i < l.length) :
    ∃ A D C, l = A ++ D ++ C ∧ putList l i ex x = A ++ [x] ++ C ∧
      ∀ w ∈ D, ex = true ∧ l[i]? = some w := by
  unfold putList
  cases ex with
  | true =>
    have h := hi rfl
    refine ⟨l.take i, [l[i]], l.drop (i + 1), ?_, ?_, ?_⟩
    · simp
    · rw [List.set_eq_take_append_cons_drop]; simp [h]
    · intro w hw; simp at hw; subst hw; exact ⟨rfl, List.getElem?_eq_getElem h⟩
  | false =>
    refine ⟨l.take i, [], l.drop i, by simp, by simp, by simp⟩

/-- The records `B1`, `B2` agree on what the shape reads. -/
def shapeEq (B1 B2 : BRec) : Prop :=
  B1.bv.rootNode' = B2.bv.rootNode' ∧ B1.ib.root' = B2.ib.root' ∧ B1.ns = B2.ns ∧ B1.nm = B2.nm ∧
    B1.bm = B2.bm

theorem bktKeys_shapeEq (W : WView) (B1 B2 : BRec) (h : shapeEq B1 B2) :
    bktKeys W B1 ↔ bktKeys W B2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold bktKeys bktKeysB nodeKeys
  rw [h1, h2, h3, h4]

theorem entryIn_shapeEq (W : WView) (B1 B2 : BRec) (h : shapeEq B1 B2) (k v : List w8) :
    entryIn W B1 k v ↔ entryIn W B2 k v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold entryIn posRoot pagePosAt
  rw [h1, h2, h3, h4]

end leafop

section leaftoks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem bktToks_shapeEq (γ : GName) (W : WView) (B1 B2 : BRec) (h : shapeEq B1 B2) :
    bktToks (GF := GF) γ W B1 ⊣⊢ bktToks γ W B2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold bktToks nodeToks opened
  rw [h1, h2, h3, h4, h5]
  exact .rfl

theorem bigSepL_mid {A : Type} (Φ : A → IProp GF) (X D C E : List A) (hE : ∀ w ∈ E, emp ⊢ Φ w) :
    ([∗list] w ∈ X ++ D ++ C, Φ w) ⊢ [∗list] w ∈ X ++ E ++ C, Φ w := by
  have hE' : (emp : IProp GF) ⊢ [∗list] w ∈ E, Φ w :=
    (BigSepL.bigSepL_emp (PROP := IProp GF) (l := E)).2.trans
      (BigSepL.bigSepL_mono (fun {k x} h => hE x (List.mem_of_getElem? h)))
  iintro H
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H3⟩
  icases BigSepL.bigSepL_append.1 $$ H1 with ⟨H1, -⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iexact H1
    · iapply hE'
      iempintro
  · iexact H3

/-- The leaf's entries changed (`E` no nested bucket stored in pages): its tokens stay. -/
theorem nodeToks_leafOp2 (γ : GName) (W : WView) (B : BRec) (r r' : NRec)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, isBktFlag w.flags → inBucketRoot w.value = 0) :
    nodeToks (GF := GF) γ W B r ⊢ nodeToks γ W B r' := by
  unfold nodeToks
  rw [e3, e1, hleaf, hws, hws']
  iintro ⟨Hp, Hl⟩
  iframe Hp
  iapply bigSepL_mid _ A D C E ?_ $$ Hl
  intro w hw
  rw [if_pos rfl, if_neg (fun h => h.2.1 (hE w hw h.1))]
  try exact .rfl

theorem bktToks_leafOp2 (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (hc : bktClean W hwm bl B) (l : Loc) (r r' : NRec) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid')
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, isBktFlag w.flags → inBucketRoot w.value = 0) :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W { B with ns := <[l := r']> B.ns } := by
  have hrn : B.bv.rootNode' ≠ null := by
    intro h; rw [(hc.2.2.1 h).1] at hr; cases hr
  have hns : ∀ r0, nodeToks (GF := GF) γ W { B with ns := <[l := r']> B.ns } r0 = nodeToks γ W B r0 :=
    fun _ => rfl
  unfold bktToks
  simp only [if_neg hrn, hns]
  iintro H
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
    (show Std.get? B.ns l = some r from hr)) $$ H with ⟨Hn, Hback⟩
  ihave Hn := nodeToks_leafOp2 γ W B r r' hleaf e1 e3 A D C E hws hws' hE $$ Hn
  iapply Hback $$ %r' Hn

end leaftoks

section pk
variable [ext : FfiSyntax]

/-- The entry `i` of a leaf has the key the cursor searched for: it is the one returned
(`pathKey`). -/
theorem pathKey_at (ws : List WEntry) (i : Nat) (w : WEntry) (kb kbs : List w8) (f : w32)
    (hw : ws[i]? = some w) (hk : wKey ws i = kb)
    (hP : ∀ w ∈ ws, w.key = kb → w.flags = f ∧ kbs = kb) : w.flags = f ∧ kbs = kb :=
  hP w (List.mem_of_getElem? hw) (by simpa [wKey, hw] using hk)

end pk

section acc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A key a writer's cursor returned, with its bytes (`keySrcIs`), lent out (and back). -/
theorem keySrcIs_acc (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (k : GoSlice) (kbs : List w8) (hc : W.data.locCar ≠ 0)
    (h : keySrcIs W B k kbs) :
    wctx (GF := GF) W bl B txl pmap pm dqp ⊢ ∃ (dq : DFrac), k ↦*{dq} kbs ∗
      (k ↦*{dq} kbs -∗ wctx W bl B txl pmap pm dqp) := by
  iintro Hctx
  rcases h with ⟨rfl, rfl⟩ | ⟨l, r, i, it, w, hr, hit, hw, rfl, hns, rfl⟩ |
    ⟨pid, p, pg, off, n, hpa, hinl, hlen, hb, hn, rfl, rfl⟩
  · iexists DFrac.own 1
    isplitl []
    · iapply ownSlice_nil
    iintro -; iexact Hctx
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases bktOwn_node_acc W bl B l r hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) hit hw $$ Hents
      with ⟨Hi, Hentsback⟩
    isimp only [wOwn] at Hi
    icases Hi with ⟨%Hfp, Hk, Hvv⟩
    icases srcBorrow W hc W.q it.key' w.ks w.key hns $$ [Hpv Hk] with ⟨%dq, -, Hk, Hkback⟩
    · iframe
    iexists dq
    iframe Hk
    iintro Hk
    ihave Hk := Hkback $$ Hk
    icases Hk with ⟨Hpv, Hk⟩
    ihave Hents := Hentsback $$ [Hk Hvv]
    · unfold wOwn; iframe; ipureintro; exact Hfp
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l r hr]
    iframe
    unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    isimp only [bktOwn] at Hb
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    have Hne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    icases wpageAt_acc W B pid p pg hc hpa hinl Hne $$ [Hpv Hpo] with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    icases bytes_slice_acc (hG := hG) p dq pg off n hb hn Hc $$ Hpg with ⟨Hk, Hkback⟩
    iexists dq
    iframe Hk
    iintro Hk
    ihave Hpg := Hkback $$ Hk
    ihave Hpg := Hpgback $$ Hpg
    icases Hpg with ⟨Hpv, Hpo⟩
    unfold bktOwn wView; iframe; iframe #; ipureintro; exact Hlgv

end acc

end ShapeOpen

end bbolt
end EtcdGrove
end Perennial
