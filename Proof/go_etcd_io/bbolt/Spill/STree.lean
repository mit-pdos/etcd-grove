/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 2: **a strict subtree**
(`sTree P hwm id lo hi h S`), what the spill writes and what it keeps of the base tree: the
tree of page `id` of the page map `P` is well-formed below `hwm`, its keys a B+tree's in
`[lo, hi)`, its pages exactly `S`, each good and sharing no page with a sibling's tree, of
height `h` (uniform leaf depth, a height function over `S`), and their extents pairwise
disjoint below `hwm`. A whole tree that is an `sTree` is `treeOK` (`treeOK_of_sTree`), over its
own pages (`treePages`, which `spillC` takes).

The other parts build `sTree`s: from a page and its children's (`Spill/STreeBuild`), from the
base tree (`Spill/STreeBase`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.TreeAgree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Spill

section stree
variable [GooseExts]

/-- `viewUnique`'s clause for the page `id` (bytes `pg`): the trees of its children (a branch)
or of its nested buckets (a leaf) are pairwise disjoint and do not hold it. -/
def uniqAt (P : Pages) (id : Nat) (pg : List w8) : Prop :=
  (pageFlags pg = branchPageFlag →
    (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → ∀ d,
      treeHas P (branchPgid pg i) d → ¬ treeHas P (branchPgid pg j) d) ∧
    (∀ i < pageCount pg, ¬ treeHas P (branchPgid pg i) id)) ∧
  (pageFlags pg = leafPageFlag →
    (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → leafFlags pg i % 2 = bucketLeafFlag →
      leafFlags pg j % 2 = bucketLeafFlag → ∀ d, bucketHas P (leafValue pg i) d →
        ¬ bucketHas P (leafValue pg j) d) ∧
    (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
      ¬ bucketHas P (leafValue pg i) id))

/-- `pageHts`' clause for the page `id` (bytes `pg`) and the heights `pht`. -/
def htAt (pht : Nat → Nat) (id : Nat) (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → pht id = 0) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, pht (branchPgid pg i) + 1 = pht id)

/-- Two pages' extents do not overlap. -/
def extDisj (x : Nat) (pgx : List w8) (y : Nat) (pgy : List w8) : Prop :=
  x + (1 + pageOverflow pgx) ≤ y ∨ y + (1 + pageOverflow pgy) ≤ x

/-- **A strict subtree** (see the module doc). -/
structure sTree (P : Pages) (hwm id : Nat) (lo hi : Option (List w8)) (h : Nat) (S : List Nat) :
    Prop where
  wf : treeWF P hwm id
  keys : treeKeys P id lo hi
  has : ∀ x, treeHas P id x ↔ x ∈ S
  nodup : S.Nodup
  good : ∀ x ∈ S, ∀ pg, P !! x = some pg → pageGood pg
  uniq : ∀ x ∈ S, ∀ pg, P !! x = some pg → uniqAt P x pg
  hts : ∃ pht : Nat → Nat, (∀ x ∈ S, ∀ pg, P !! x = some pg → htAt pht x pg) ∧ pht id = h
  disj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ pgx pgy, P !! x = some pgx → P !! y = some pgy →
    extDisj x pgx y pgy
  ext : ∀ x ∈ S, ∀ pg, P !! x = some pg → x + (1 + pageOverflow pg) ≤ hwm

/-! ## `treePages` -/

open Classical in
theorem treePages_lookup (P : Pages) (root id : Nat) :
    treePages P root !! id = if treeHas P root id then P !! id else none := by
  unfold treePages
  rw [GMap.lookup_filter]
  cases P !! id with
  | none => split <;> rfl
  | some v => by_cases h : treeHas P root id <;> simp [h, Option.filter]

theorem treePages_le (P : Pages) (root : Nat) : pagesLe (treePages P root) P := by
  intro id pg h
  rw [treePages_lookup] at h
  split at h
  · exact h
  · cases h

/-- The tree's own pages agree with `P` on the tree. -/
theorem treePages_agree (P : Pages) (root : Nat) :
    ∀ id, treeHas P root id → treePages P root !! id = P !! id := by
  intro id h
  rw [treePages_lookup]; simp [h]

/-- The tree of `root` in its own pages is its tree in `P`. -/
theorem treeHas_treePages (P : Pages) (root id : Nat) :
    treeHas (treePages P root) root id ↔ treeHas P root id :=
  ⟨treeHas_le (treePages_le P root), treeHas_agree (treePages_agree P root)⟩

/-- A subtree's pages are the tree's (`treeHas` is transitive). -/
theorem treeHas_trans {P : Pages} {a b c : Nat} (h1 : treeHas P a b) (h2 : treeHas P b c) :
    treeHas P a c := by
  have key : ∀ {a b}, treeHas P a b → ∀ c, treeHas P b c → treeHas P a c := fun {a b} h =>
    treeHas.rec (pages := P)
      (motive_1 := fun a b _ => ∀ c, treeHas P b c → treeHas P a c)
      (motive_2 := fun pg b _ => ∀ c, treeHas P b c → pageHas P pg c)
      (motive_3 := fun v b _ => ∀ c, treeHas P b c → bucketHas P v c)
      (fun _ _ _ c h => h)
      (fun a pg b hpg _ ih c h => treeHas.sub a pg c hpg (ih c h))
      (fun pg i b hfl hi _ ih c h => pageHas.child pg i c hfl hi (ih c h))
      (fun pg i b hfl hi hbf _ ih c h => pageHas.bucket pg i c hfl hi hbf (ih c h))
      (fun v b hr _ ih c h => bucketHas.file v c hr (ih c h))
      (fun v b hr _ ih c h => bucketHas.inline v c hr (ih c h))
      h
  exact key h1 c h2

/-- `treePages` of its own result is itself. -/
theorem treePages_idem (P : Pages) (root : Nat) :
    treePages (treePages P root) root = treePages P root := by
  apply GMap.ext
  intro id
  show treePages (treePages P root) root !! id = treePages P root !! id
  rw [treePages_lookup (treePages P root), treeHas_treePages]
  rw [treePages_lookup P root]
  by_cases h : treeHas P root id <;> simp [h]

/-! ## A whole tree that is an `sTree` is `treeOK` -/

/-- `uniqAt` holds in a map whose trees, from the page's children and nested buckets, are the
same. -/
theorem uniqAt_congr {P P' : Pages} {id : Nat} {pg : List w8}
    (hT : ∀ i < pageCount pg, pageFlags pg = branchPageFlag → ∀ d,
      treeHas P' (branchPgid pg i) d ↔ treeHas P (branchPgid pg i) d)
    (hB : ∀ i < pageCount pg, pageFlags pg = leafPageFlag → leafFlags pg i % 2 = bucketLeafFlag →
      ∀ d, bucketHas P' (leafValue pg i) d ↔ bucketHas P (leafValue pg i) d)
    (hu : uniqAt P id pg) : uniqAt P' id pg := by
  refine ⟨fun hb => ⟨fun i j hi hj hij d h1 h2 => ?_, fun i hi h => ?_⟩,
    fun hl => ⟨fun i j hi hj hij hbi hbj d h1 h2 => ?_, fun i hi hbi h => ?_⟩⟩
  · exact (hu.1 hb).1 i j hi hj hij d ((hT i hi hb d).1 h1) ((hT j hj hb d).1 h2)
  · exact (hu.1 hb).2 i hi ((hT i hi hb id).1 h)
  · exact (hu.2 hl).1 i j hi hj hij hbi hbj d ((hB i hi hl hbi d).1 h1) ((hB j hj hl hbj d).1 h2)
  · exact (hu.2 hl).2 i hi hbi ((hB i hi hl hbi id).1 h)

/-- The tree of a branch's child is in the branch's tree. -/
theorem treeHas_child {P : Pages} {r : Nat} {pg : List w8} (hpg : P !! r = some pg)
    (hfl : pageFlags pg = branchPageFlag) {i : Nat} (hi : i < pageCount pg) {d : Nat}
    (h : treeHas P (branchPgid pg i) d) : treeHas P r d :=
  treeHas.sub r pg d hpg (pageHas.child pg i d hfl hi h)

/-- The tree of a leaf's nested bucket is in the leaf's tree. -/
theorem treeHas_bucket {P : Pages} {r : Nat} {pg : List w8} (hpg : P !! r = some pg)
    (hfl : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) {d : Nat}
    (h : bucketHas P (leafValue pg i) d) : treeHas P r d :=
  treeHas.sub r pg d hpg (pageHas.bucket pg i d hfl hi hbf h)

/-- `bucketHas` in the tree's own pages, for a nested bucket of a page of the tree. -/
theorem bucketHas_treePages {P : Pages} {root r : Nat} {pg : List w8} (hr : treeHas P root r)
    (hpg : P !! r = some pg) (hfl : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) (d : Nat) :
    bucketHas (treePages P root) (leafValue pg i) d ↔ bucketHas P (leafValue pg i) d :=
  ⟨bucketHas_le (treePages_le P root), bucketHas_agree fun y hy =>
    treePages_agree P root y (treeHas_trans hr (treeHas_bucket hpg hfl hi hbf hy))⟩

/-- The same for a branch's child. -/
theorem treeHas_child_treePages {P : Pages} {root r : Nat} {pg : List w8} (hr : treeHas P root r)
    (hpg : P !! r = some pg) (hfl : pageFlags pg = branchPageFlag) {i : Nat}
    (hi : i < pageCount pg) (d : Nat) :
    treeHas (treePages P root) (branchPgid pg i) d ↔ treeHas P (branchPgid pg i) d :=
  ⟨treeHas_le (treePages_le P root), treeHas_agree fun y hy =>
    treePages_agree P root y (treeHas_trans hr (treeHas_child hpg hfl hi hy))⟩

/-- **A whole tree that is an `sTree` is `treeOK`** over its own pages, given its root's shape
(`rootShape`) and a txid below `2 ^ 63`. -/
theorem treeOK_of_sTree {P : Pages} {h : Nat} {S : List Nat} (C : CommitSt)
    (hs : sTree P C.hwm C.root none none h S) (hpages : C.pages = treePages P C.root)
    (hshape : rootShape C.pages C.root) (htx : C.txid < 2 ^ 63) : treeOK C := by
  obtain ⟨m0, m1, pages, root, hwm, txid, flpg⟩ := C
  simp only at hs hpages hshape htx ⊢
  subst hpages
  have hag := treePages_agree P root
  have hle := treePages_le P root
  -- a page of the tree's own pages is a page of the tree
  have hin : ∀ id pg, treePages P root !! id = some pg → treeHas P root id ∧ P !! id = some pg := by
    intro id pg h
    rw [treePages_lookup] at h
    split at h
    · exact ⟨by assumption, h⟩
    · cases h
  obtain ⟨pht, hpht, -⟩ := hs.hts
  refine ⟨⟨treeWF_agree hs.wf hag, ⟨fun id pg h => ?_, ?_, ?_⟩, treeKeys_agree hs.keys hag,
    pht, fun id pg h => ?_⟩, treePages_idem P root, ?_, ?_, hshape, htx⟩
  · obtain ⟨ht, hp⟩ := hin id pg h
    exact hs.good id ((hs.has id).1 ht) pg hp
  · intro id pg h hfl
    obtain ⟨ht, hp⟩ := hin id pg h
    have hu := uniqAt_congr (P' := treePages P root)
      (fun i hi hb d => treeHas_child_treePages ht hp hb hi d)
      (fun i hi hl hbf d => bucketHas_treePages ht hp hl hi hbf d)
      (hs.uniq id ((hs.has id).1 ht) pg hp)
    exact hu.1 hfl
  · intro id pg h hfl
    obtain ⟨ht, hp⟩ := hin id pg h
    have hu := uniqAt_congr (P' := treePages P root)
      (fun i hi hb d => treeHas_child_treePages ht hp hb hi d)
      (fun i hi hl hbf d => bucketHas_treePages ht hp hl hi hbf d)
      (hs.uniq id ((hs.has id).1 ht) pg hp)
    exact hu.2 hfl
  · obtain ⟨ht, hp⟩ := hin id pg h
    exact hpht id ((hs.has id).1 ht) pg hp
  · intro id1 pg1 id2 pg2 h1 h2 hne
    obtain ⟨ht1, hp1⟩ := hin id1 pg1 h1
    obtain ⟨ht2, hp2⟩ := hin id2 pg2 h2
    exact hs.disj id1 ((hs.has id1).1 ht1) id2 ((hs.has id2).1 ht2) hne pg1 pg2 hp1 hp2
  · intro id pg h
    obtain ⟨ht, hp⟩ := hin id pg h
    exact hs.ext id ((hs.has id).1 ht) pg hp

end stree

end Spill

end bbolt
end EtcdGrove
end Perennial
