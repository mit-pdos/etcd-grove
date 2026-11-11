/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 4: building an `sTree` from
a written page and its subtrees: a branch page over its children's `sTree`s (`sTree_branch`), a
leaf page over its nested buckets' (`sTree_leaf`), the subtrees' pages pairwise disjoint and
apart from the page.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeMono

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Spill

section build
variable [GooseExts]

/-- An `sTree`'s root is a leaf iff its height is `0`. -/
theorem sTree_leaf_iff {P : Pages} {hwm r : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm r lo hi h S) {pg : List w8} (hpg : P !! r = some pg) :
    pageFlags pg = leafPageFlag ↔ h = 0 := by
  obtain ⟨pht, hpht, hr⟩ := hs.hts
  have hrS : r ∈ S := (hs.has r).1 (treeHas.root r pg hpg)
  have ht := hpht r hrS pg hpg
  obtain ⟨-, -, -, -, hfl⟩ := Read.treeWF_page P hwm r hs.wf pg hpg
  constructor
  · intro hl; rw [← hr]; exact ht.1 hl
  · intro h0
    rcases hfl with hb | hl
    · exfalso
      have hbw : 0 < pageCount pg := by
        cases hs.wf with
        | page _ pg' _ _ hpg' _ _ hpt =>
          rw [hpg] at hpg'; cases hpg'
          cases hpt with
          | leaf _ _ hfl' _ _ => rw [hb] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
          | branch _ _ _ hbw _ => exact hbw.1
      have := ht.2 hb 0 hbw
      omega
    · exact hl

/-- A well-formed tree's root is a page. -/
theorem treeWF_page_some {P : Pages} {hwm r : Nat} (h : treeWF P hwm r) : ∃ pg, P !! r = some pg := by
  cases h with
  | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩

/-- `l.Pairwise R` from `R` on every pair of distinct indices in order. -/
theorem pairwise_range {R : Nat → Nat → Prop} (n : Nat) (h : ∀ i j, i < j → j < n → R i j) :
    (List.range n).Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  simp only [List.length_range] at hj
  exact h i j hij hj

/-- The pages of a page and its subtrees `Sc i` (`i < n`). -/
def nodePages (id n : Nat) (Sc : Nat → List Nat) : List Nat :=
  id :: (List.range n).flatMap Sc

theorem mem_nodePages {id n : Nat} {Sc : Nat → List Nat} {x : Nat} :
    x ∈ nodePages id n Sc ↔ x = id ∨ ∃ i < n, x ∈ Sc i := by
  simp [nodePages]

/-- The subtrees' pages are pairwise disjoint, apart from the page, extents too. -/
structure subsDisj (P : Pages) (id : Nat) (pg : List w8) (n : Nat) (Sc : Nat → List Nat) :
    Prop where
  pages : ∀ i j, i < n → j < n → i ≠ j → ∀ x ∈ Sc i, x ∉ Sc j
  own : ∀ i < n, id ∉ Sc i
  ext : ∀ i j, i < n → j < n → i ≠ j → ∀ x ∈ Sc i, ∀ y ∈ Sc j, ∀ pgx pgy,
    P !! x = some pgx → P !! y = some pgy → extDisj x pgx y pgy
  ownExt : ∀ i < n, ∀ x ∈ Sc i, ∀ pgx, P !! x = some pgx → extDisj id pg x pgx

theorem nodePages_nodup {P : Pages} {id : Nat} {pg : List w8} {n : Nat} {Sc : Nat → List Nat}
    (hd : subsDisj P id pg n Sc) (hnd : ∀ i < n, (Sc i).Nodup) : (nodePages id n Sc).Nodup := by
  unfold nodePages
  rw [List.nodup_cons]
  refine ⟨fun hm => ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_range] at hm
    obtain ⟨i, hi, hx⟩ := hm
    exact hd.own i hi hx
  · unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun i hi => hnd i (List.mem_range.1 hi), pairwise_range n fun i j hij hj => ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact hd.pages i j (by omega) hj (by omega) x hx hy

/-- The combined height function: the subtrees' on their pages, `h0` elsewhere. -/
def phtJoin (n : Nat) (Sc : Nat → List Nat) (phts : Nat → Nat → Nat) (h0 : Nat) (x : Nat) : Nat :=
  open Classical in
  if hx : ∃ i, i < n ∧ x ∈ Sc i then phts (Classical.choose hx) x else h0

theorem phtJoin_sub {n : Nat} {Sc : Nat → List Nat} {phts : Nat → Nat → Nat} {h0 : Nat}
    (hdp : ∀ i j, i < n → j < n → i ≠ j → ∀ x ∈ Sc i, x ∉ Sc j) {i x : Nat} (hi : i < n)
    (hx : x ∈ Sc i) : phtJoin n Sc phts h0 x = phts i x := by
  unfold phtJoin
  have he : ∃ i, i < n ∧ x ∈ Sc i := ⟨i, hi, hx⟩
  rw [dite_eq_left_of_eq_true (eq_true he)]
  have hc := Classical.choose_spec he
  by_cases hji : Classical.choose he = i
  · rw [hji]
  · exact absurd hc.2 (hdp i _ hi hc.1 (Ne.symm hji) x hx)

theorem phtJoin_own {n : Nat} {Sc : Nat → List Nat} {phts : Nat → Nat → Nat} {h0 : Nat} {id : Nat}
    (hown : ∀ i < n, id ∉ Sc i) : phtJoin n Sc phts h0 id = h0 := by
  unfold phtJoin
  rw [dite_eq_right_of_eq_false (eq_false ?_)]
  rintro ⟨i, hi, hx⟩
  exact hown i hi hx

/-- **A branch page over its children's `sTree`s** (each of height `h`, keys within the entry's
bounds, first key the entry's) is an `sTree` of height `h + 1`. -/
theorem sTree_branch {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {pg : List w8} (Sc : Nat → List Nat)
    (hpg : P !! id = some pg) (hfl : pageFlags pg = branchPageFlag) (h2 : 2 ≤ id)
    (hlt : id < hwm) (hid : pageId pg = id) (hlen : pg.length = (1 + pageOverflow pg) * 4096)
    (hbw : branchWF pg pg.length hwm) (hgood : pageGood pg) (hc2 : 2 ≤ pageCount pg)
    (hkin : ∀ i < pageCount pg, keyIn lo hi (branchKey pg i))
    (hch : ∀ i < pageCount pg, sTree P hwm (branchPgid pg i) (childLo lo (branchKey pg) i)
      (childHi hi (branchKey pg) (pageCount pg) i) h (Sc i))
    (hfirst : ∀ i < pageCount pg, ∃ cpg, P !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
      pageKey cpg 0 = branchKey pg i)
    (hd : subsDisj P id pg (pageCount pg) Sc)
    (hext : id + (1 + pageOverflow pg) ≤ hwm) :
    sTree P hwm id lo hi (h + 1) (nodePages id (pageCount pg) Sc) := by
  have hroot : ∀ i (hi : i < pageCount pg), branchPgid pg i ∈ Sc i := fun i hi => by
    obtain ⟨cpg, hc, -⟩ := hfirst i hi
    exact ((hch i hi).has _).1 (treeHas.root _ cpg hc)
  -- the pages of the tree
  have hhas : ∀ x, treeHas P id x ↔ x ∈ nodePages id (pageCount pg) Sc := by
    intro x
    rw [mem_nodePages]
    constructor
    · intro ht
      cases ht with
      | root _ _ _ => exact Or.inl rfl
      | sub _ pg' _ hpg' hp =>
        rw [hpg] at hpg'; cases hpg'
        cases hp with
        | child _ i _ _ hi hc => exact Or.inr ⟨i, hi, ((hch i hi).has x).1 hc⟩
        | bucket _ i _ hfl' _ _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
    · rintro (rfl | ⟨i, hi, hx⟩)
      · exact treeHas.root x pg hpg
      · exact treeHas_child hpg hfl hi (((hch i hi).has x).2 hx)
  -- a page of a subtree
  have hsub : ∀ x, x ∈ nodePages id (pageCount pg) Sc → x ≠ id → ∃ i < pageCount pg, x ∈ Sc i := by
    intro x hx hne
    rcases mem_nodePages.1 hx with rfl | h'
    · exact absurd rfl hne
    · exact h'
  -- the kind of the children
  have hkind : ∀ i < pageCount pg, ∃ cpg, P !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
      pageFlags cpg = (if h = 0 then leafPageFlag else branchPageFlag) ∧
      pageKey cpg 0 = branchKey pg i := by
    intro i hi
    obtain ⟨cpg, hc, h0, hk⟩ := hfirst i hi
    refine ⟨cpg, hc, h0, ?_, hk⟩
    have hl := sTree_leaf_iff (hch i hi) hc
    obtain ⟨-, -, -, -, hf⟩ := Read.treeWF_page P hwm _ (hch i hi).wf cpg hc
    by_cases h0' : h = 0
    · simp only [h0', ite_true]; exact hl.2 h0'
    · simp only [h0', ite_false]
      rcases hf with hf | hf
      · exact hf
      · exact absurd (hl.1 hf) h0'
  -- heights
  have hphts : ∀ i, ∃ pht : Nat → Nat, i < pageCount pg →
      (∀ x ∈ Sc i, ∀ pg', P !! x = some pg' → htAt pht x pg') ∧ pht (branchPgid pg i) = h := by
    intro i
    by_cases hi : i < pageCount pg
    · obtain ⟨pht, h1, h2⟩ := (hch i hi).hts
      exact ⟨pht, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun x => x, fun h' => absurd h' hi⟩
  have hphts' := fun i => Classical.choose_spec (hphts i)
  generalize hphdef : (fun i => Classical.choose (hphts i)) = phts at hphts'
  replace hphts : ∀ i, i < pageCount pg →
      (∀ x ∈ Sc i, ∀ pg', P !! x = some pg' → htAt (phts i) x pg') ∧
        phts i (branchPgid pg i) = h := by
    intro i; rw [← hphdef]; exact hphts' i
  clear hphts' hphdef
  refine ⟨treeWF.page id pg h2 hlt hpg hid hlen
      (pageTreeWF.branch pg pg.length hfl hbw fun i hi => (hch i hi).wf),
    treeKeys.branch id pg lo hi _ hpg hfl hc2 hkin hkind fun i hi => (hch i hi).keys,
    hhas, nodePages_nodup hd fun i hi => (hch i hi).nodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp; exact hgood
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      exact (hch i hi).good x hxs pg' hp
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp
      refine ⟨fun _ => ⟨fun i j hi hj hij d h1 h2 => ?_, fun i hi h1 => ?_⟩, fun hl => ?_⟩
      · exact hd.pages i j hi hj hij d (((hch i hi).has d).1 h1) (((hch j hj).has d).1 h2)
      · exact hd.own i hi (((hch i hi).has x).1 h1)
      · rw [hfl] at hl; simp [branchPageFlag, leafPageFlag] at hl
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      exact (hch i hi).uniq x hxs pg' hp
  · refine ⟨phtJoin (pageCount pg) Sc phts (h + 1), fun x hx pg' hp => ?_,
      phtJoin_own hd.own⟩
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp
      refine ⟨fun hl => by rw [hfl] at hl; simp [branchPageFlag, leafPageFlag] at hl,
        fun _ i hi => ?_⟩
      rw [phtJoin_own hd.own, phtJoin_sub hd.pages hi (hroot i hi), ((hphts i) hi).2]
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      have hat := ((hphts i) hi).1 x hxs pg' hp
      have hxt : treeHas P (branchPgid pg i) x := ((hch i hi).has x).2 hxs
      refine ⟨fun hl => by rw [phtJoin_sub hd.pages hi hxs]; exact hat.1 hl, fun hb k hk => ?_⟩
      have hw := Read.treeHas_treeWF P hwm hxt (hch i hi).wf
      obtain ⟨cpg, hc⟩ := treeWF_page_some (treeWF_branch_child hw hp hb hk)
      have hck : branchPgid pg' k ∈ Sc i := ((hch i hi).has _).1
        (treeHas_trans hxt (treeHas_child hp hb hk (treeHas.root _ cpg hc)))
      rw [phtJoin_sub hd.pages hi hxs, phtJoin_sub hd.pages hi hck]
      exact hat.2 hb k hk
  · intro x hx y hy hne pgx pgy hpx hpy
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hpx; cases hpx
      obtain ⟨j, hj, hys⟩ := hsub y hy (Ne.symm hne)
      exact hd.ownExt j hj y hys pgy hpy
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      by_cases hyi : y = id
      · subst hyi; rw [hpg] at hpy; cases hpy
        have := hd.ownExt i hi x hxs pgx hpx
        unfold extDisj at this ⊢; omega
      · obtain ⟨j, hj, hys⟩ := hsub y hy hyi
        by_cases hij : i = j
        · subst hij; exact (hch i hi).disj x hxs y hys hne pgx pgy hpx hpy
        · exact hd.ext i j hi hj hij x hxs y hys pgx pgy hpx hpy
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp; exact hext
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      exact (hch i hi).ext x hxs pg' hp

/-- **A nested bucket's value as the spill leaves it**: inline (a good inline page, no pages), or
a file bucket whose tree is an `sTree` with the pages `S`. -/
def bvalS (P : Pages) (hwm : Nat) (v : List w8) (S : List Nat) : Prop :=
  16 ≤ v.length ∧
  ((inBucketRoot v = 0 ∧ S = [] ∧ inlineGood (inlinePage v)) ∨
   (inBucketRoot v ≠ 0 ∧ ∃ h, sTree P hwm (inBucketRoot v) none none h S))

/-- A good inline page reaches no page. -/
theorem inlineGood_noHas {P : Pages} {v : List w8} (hg : inlineGood (inlinePage v))
    (hr : inBucketRoot v = 0) (d : Nat) : ¬ bucketHas P v d := by
  intro h
  cases h with
  | file _ _ hr' _ => exact hr' hr
  | inline _ _ _ hp =>
    cases hp with
    | child _ _ _ hfl _ _ =>
      rw [hg.2.1] at hfl; simp [branchPageFlag, leafPageFlag] at hfl
    | bucket _ i _ _ hi hbf _ =>
      have := (hg.2.2.2.2 i hi).2
      rw [this] at hbf; simp [bucketLeafFlag] at hbf

/-- A nested bucket's pages are its `bvalS` pages. -/
theorem bvalS_has {P : Pages} {hwm : Nat} {v : List w8} {S : List Nat} (hb : bvalS P hwm v S)
    (d : Nat) : bucketHas P v d ↔ d ∈ S := by
  rcases hb.2 with ⟨hr, rfl, hg⟩ | ⟨hr, h, hs⟩
  · exact ⟨fun h => absurd h (inlineGood_noHas hg hr d), fun h => by simp at h⟩
  · constructor
    · intro h
      cases h with
      | file _ _ _ ht => exact (hs.has d).1 ht
      | inline _ _ hr' _ => exact absurd hr' hr
    · intro h
      exact bucketHas.file v d hr ((hs.has d).2 h)

/-- A nested bucket's value is well-formed. -/
theorem bvalS_wf {P : Pages} {hwm : Nat} {v : List w8} {S : List Nat} (hb : bvalS P hwm v S) :
    bucketWF P hwm v := by
  rcases hb.2 with ⟨hr, -, hg⟩ | ⟨hr, h, hs⟩
  · refine bucketWF.inline v hb.1 hr hg.2.1 (pageTreeWF.leaf _ _ hg.2.1 hg.2.2.1 fun i hi hbf => ?_)
    have := (hg.2.2.2.2 i hi).2
    rw [this] at hbf; simp [bucketLeafFlag] at hbf
  · exact bucketWF.file v hb.1 hr hs.wf

/-- **A leaf page over its nested buckets' values** is an `sTree` of height `0`. -/
theorem sTree_leaf {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {pg : List w8}
    (Sb : Nat → List Nat)
    (hpg : P !! id = some pg) (hfl : pageFlags pg = leafPageFlag) (h2 : 2 ≤ id)
    (hlt : id < hwm) (hid : pageId pg = id) (hlen : pg.length = (1 + pageOverflow pg) * 4096)
    (hlw : leafWF pg pg.length) (hgood : pageGood pg)
    (hkin : ∀ i < pageCount pg, keyIn lo hi (leafKey pg i))
    (hb : ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
      bvalS P hwm (leafValue pg i) (Sb i))
    (hb0 : ∀ i < pageCount pg, leafFlags pg i % 2 ≠ bucketLeafFlag → Sb i = [])
    (hd : subsDisj P id pg (pageCount pg) Sb)
    (hext : id + (1 + pageOverflow pg) ≤ hwm) :
    sTree P hwm id lo hi 0 (nodePages id (pageCount pg) Sb) := by
  -- a nested bucket's pages
  have hbS : ∀ i < pageCount pg, ∀ d, leafFlags pg i % 2 = bucketLeafFlag →
      (bucketHas P (leafValue pg i) d ↔ d ∈ Sb i) := fun i hi d hbf => bvalS_has (hb i hi hbf) d
  have hSb : ∀ i < pageCount pg, ∀ d, d ∈ Sb i → leafFlags pg i % 2 = bucketLeafFlag := by
    intro i hi d hd'
    by_cases hn : leafFlags pg i % 2 = bucketLeafFlag
    · exact hn
    · rw [hb0 i hi hn] at hd'; simp at hd'
  have hhas : ∀ x, treeHas P id x ↔ x ∈ nodePages id (pageCount pg) Sb := by
    intro x
    rw [mem_nodePages]
    constructor
    · intro ht
      cases ht with
      | root _ _ _ => exact Or.inl rfl
      | sub _ pg' _ hpg' hp =>
        rw [hpg] at hpg'; cases hpg'
        cases hp with
        | child _ i _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
        | bucket _ i _ _ hi hbf hbh => exact Or.inr ⟨i, hi, (hbS i hi x hbf).1 hbh⟩
    · rintro (rfl | ⟨i, hi, hx⟩)
      · exact treeHas.root x pg hpg
      · have hbf := hSb i hi x hx
        exact treeHas_bucket hpg hfl hi hbf ((hbS i hi x hbf).2 hx)
  have hsub : ∀ x, x ∈ nodePages id (pageCount pg) Sb → x ≠ id → ∃ i < pageCount pg, x ∈ Sb i := by
    intro x hx hne
    rcases mem_nodePages.1 hx with rfl | h'
    · exact absurd rfl hne
    · exact h'
  -- a nested file bucket of a page of `Sb i`
  have hfile : ∀ i < pageCount pg, ∀ x ∈ Sb i, ∃ hb, sTree P hwm (inBucketRoot (leafValue pg i))
      none none hb (Sb i) := by
    intro i hi x hx
    rcases (hb i hi (hSb i hi x hx)).2 with ⟨-, he, -⟩ | ⟨-, h, hs⟩
    · rw [he] at hx; simp at hx
    · exact ⟨h, hs⟩
  have hphts : ∀ i, ∃ pht : Nat → Nat, i < pageCount pg → (∃ x, x ∈ Sb i) →
      ∀ x ∈ Sb i, ∀ pg', P !! x = some pg' → htAt pht x pg' := by
    intro i
    by_cases hi : i < pageCount pg
    · by_cases hne : ∃ x, x ∈ Sb i
      · obtain ⟨x, hx⟩ := hne
        obtain ⟨h, hs⟩ := hfile i hi x hx
        obtain ⟨pht, h1, -⟩ := hs.hts
        exact ⟨pht, fun _ _ => h1⟩
      · exact ⟨fun x => x, fun _ h' => absurd h' hne⟩
    · exact ⟨fun x => x, fun h' => absurd h' hi⟩
  have hphts' := fun i => Classical.choose_spec (hphts i)
  generalize hphdef : (fun i => Classical.choose (hphts i)) = phts at hphts'
  replace hphts : ∀ i, i < pageCount pg → ∀ x ∈ Sb i, ∀ pg', P !! x = some pg' →
      htAt (phts i) x pg' := by
    intro i hi x hx; rw [← hphdef]; exact hphts' i hi ⟨x, hx⟩ x hx
  clear hphts' hphdef
  refine ⟨treeWF.page id pg h2 hlt hpg hid hlen
      (pageTreeWF.leaf pg pg.length hfl hlw fun i hi hbf => bvalS_wf (hb i hi hbf)),
    treeKeys.leaf id pg lo hi hpg hfl hkin (fun i hi hbf hr => ?_),
    hhas, nodePages_nodup hd fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases (hb i hi hbf).2 with ⟨hr', -⟩ | ⟨-, h, hs⟩
    · exact absurd hr' hr
    · exact hs.keys
  · by_cases hbf : leafFlags pg i % 2 = bucketLeafFlag
    · rcases (hb i hi hbf).2 with ⟨-, he, -⟩ | ⟨-, h, hs⟩
      · rw [he]; exact List.nodup_nil
      · exact hs.nodup
    · rw [hb0 i hi hbf]; exact List.nodup_nil
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp; exact hgood
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      obtain ⟨h, hs⟩ := hfile i hi x hxs
      exact hs.good x hxs pg' hp
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp
      refine ⟨fun hb' => by rw [hfl] at hb'; simp [branchPageFlag, leafPageFlag] at hb',
        fun _ => ⟨fun i j hi hj hij hbi hbj d h1 h2 => ?_, fun i hi hbi h1 => ?_⟩⟩
      · exact hd.pages i j hi hj hij d ((hbS i hi d hbi).1 h1) ((hbS j hj d hbj).1 h2)
      · exact hd.own i hi ((hbS i hi x hbi).1 h1)
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      obtain ⟨h, hs⟩ := hfile i hi x hxs
      exact hs.uniq x hxs pg' hp
  · refine ⟨phtJoin (pageCount pg) Sb phts 0, fun x hx pg' hp => ?_, phtJoin_own hd.own⟩
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp
      exact ⟨fun _ => phtJoin_own hd.own,
        fun hb' => by rw [hfl] at hb'; simp [branchPageFlag, leafPageFlag] at hb'⟩
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      obtain ⟨h, hs⟩ := hfile i hi x hxs
      have hat := hphts i hi x hxs pg' hp
      have hxt : treeHas P (inBucketRoot (leafValue pg i)) x := (hs.has x).2 hxs
      refine ⟨fun hl => by rw [phtJoin_sub hd.pages hi hxs]; exact hat.1 hl, fun hbr k hk => ?_⟩
      have hw := Read.treeHas_treeWF P hwm hxt hs.wf
      obtain ⟨cpg, hc⟩ := treeWF_page_some (treeWF_branch_child hw hp hbr hk)
      have hck : branchPgid pg' k ∈ Sb i := (hs.has _).1
        (treeHas_trans hxt (treeHas_child hp hbr hk (treeHas.root _ cpg hc)))
      rw [phtJoin_sub hd.pages hi hxs, phtJoin_sub hd.pages hi hck]
      exact hat.2 hbr k hk
  · intro x hx y hy hne pgx pgy hpx hpy
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hpx; cases hpx
      obtain ⟨j, hj, hys⟩ := hsub y hy (Ne.symm hne)
      exact hd.ownExt j hj y hys pgy hpy
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      by_cases hyi : y = id
      · subst hyi; rw [hpg] at hpy; cases hpy
        have := hd.ownExt i hi x hxs pgx hpx
        unfold extDisj at this ⊢; omega
      · obtain ⟨j, hj, hys⟩ := hsub y hy hyi
        by_cases hij : i = j
        · subst hij
          obtain ⟨h, hs⟩ := hfile i hi x hxs
          exact hs.disj x hxs y hys hne pgx pgy hpx hpy
        · exact hd.ext i j hi hj hij x hxs y hys pgx pgy hpx hpy
  · intro x hx pg' hp
    by_cases hxi : x = id
    · subst hxi; rw [hpg] at hp; cases hp; exact hext
    · obtain ⟨i, hi, hxs⟩ := hsub x hx hxi
      obtain ⟨h, hs⟩ := hfile i hi x hxs
      exact hs.ext x hxs pg' hp

end build

end Spill

end bbolt
end EtcdGrove
end Perennial
