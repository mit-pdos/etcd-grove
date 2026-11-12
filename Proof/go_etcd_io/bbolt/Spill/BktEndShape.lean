/-
`Bucket.spill`'s root loop's end (U9x6, `notes/bbolt-proof-plan.md`): **the root shape of a written
tree from its elements** (`rootShape_of_els`, for `endEls`'s first clause). An own leaf of an
`sTree` is one of its leaves (`ownLeaf_mem_treeLeaves`, by the walk's fuel `muS`), so its elements
are among the tree's (`treeEls`); a leaf being well-formed, an element's key and value lengths are
the page's sizes.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.TreeElsFuel
public import Proof.go_etcd_io.bbolt.Spill.TreeAgree
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section shape
variable [GooseExts]

/-- An own leaf below a page of an `sTree` is in the walk from that page, with fuel above its
pages. -/
theorem ownLeaf_mem_leavesF {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) {x L : Nat} (ho : ownHas P x L) :
    ∀ n, treeHas P id x → muS P S x < n → ∀ pg, P !! L = some pg → pageFlags pg = leafPageFlag →
      pg ∈ leavesF n P x := by
  induction ho with
  | root x pgx hpg =>
    intro n _ hn pg hpg' hl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hpg] at hpg'; cases hpg'
    simp only [leavesF, hpg, hl, ↓reduceIte]; exact List.mem_singleton_self _
  | child x pgx i d hpg hfl hi hown ih =>
    intro n ht hn pg hpg' hl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hxS := (hs.has x).1 ht
    have hnl : ¬ pageFlags pgx = leafPageFlag := by
      rw [hfl]; unfold branchPageFlag leafPageFlag; decide
    obtain ⟨pgy, hpgy⟩ := ownHas_page hown
    have hxy : treeHas P x (branchPgid pgx i) :=
      treeHas.sub x pgx _ hpg (pageHas.child pgx i _ hfl hi (treeHas.root _ pgy hpgy))
    have hlt : muS P S (branchPgid pgx i) < muS P S x := by
      classical
      unfold muS
      refine filter_len_lt S _ _ ?_ x hxS ?_ ?_
      · intro e _ he
        simp only [decide_eq_true_eq] at he ⊢
        exact treeHas.sub x pgx e hpg (pageHas.child pgx i e hfl hi he)
      · simp only [decide_eq_true_eq]; exact treeHas.root x pgx hpg
      · simp only [decide_eq_false_iff_not]
        exact ((hs.uniq x hxS pgx hpg).1 hfl).2 i hi
    simp only [leavesF, hpg, hnl, ite_false]
    exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      ih m (treeHas_trans ht hxy) (by omega) pg hpg' hl⟩

/-- **An own leaf of an `sTree` is one of its leaves.** -/
theorem ownLeaf_mem_treeLeaves {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) {L : Nat} (ho : ownHas P id L) {pg : List w8}
    (hpg : P !! L = some pg) (hl : pageFlags pg = leafPageFlag) : pg ∈ treeLeaves P id := by
  have hroot : treeHas P id id := by
    cases hs.wf with | page _ pg _ _ hpg => exact treeHas.root id pg hpg
  have hmu : muS P S id ≤ S.length := by
    unfold muS; exact List.length_filter_le _ _
  have hSP : ∀ x ∈ S, (P !! x).isSome := fun x hx => treeHas_isSome ((hs.has x).2 hx)
  have h1 := length_le_size hs.nodup hSP
  exact ownLeaf_mem_leavesF hs ho _ hroot (by omega) pg hpg hl

/-- Own pages in a smaller map are own pages in the larger. -/
theorem ownHas_le {P P' : Pages} (hle : pagesLe P P') {a x : Nat} (h : ownHas P a x) :
    ownHas P' a x := by
  induction h with
  | root a pg hpg => exact ownHas.root a pg (hle a pg hpg)
  | child a pg i x hpg hf hi _ ih => exact ownHas.child a pg i x (hle a pg hpg) hf hi ih

/-- **The root shape of a written tree from its elements** (see the module doc): each element a
bucket entry, its name of `1..MaxKeySize` bytes, within `bboltEntryMax`, its nested leaves (in the
tree's pages) plain. -/
theorem rootShape_of_els {P : Pages} {hwm root : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} {E : List El} (hs : sTree P hwm root lo hi h S) (hE : treeEls P root = E)
    (hel : ∀ e ∈ E, e.1 % 2 = bucketLeafFlag ∧ (0 < e.2.1.length ∧ e.2.1.length ≤ maxKeySize) ∧
      e.2.1.length + e.2.2.length ≤ bboltEntryMax)
    (hnest : ∀ e ∈ E, ∀ bpg, bktLeafPg (treePages P root) e.2.2 bpg → ∀ j < pageCount bpg,
      leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧ leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax) :
    rootShape (treePages P root) root := by
  intro id pg hown hpg hl i hix
  have hown' := ownHas_le (treePages_le P root) hown
  have hpg' : P !! id = some pg := treePages_le P root id pg hpg
  have hmemL := ownLeaf_mem_treeLeaves hs hown' hpg' hl
  have hmem : (leafFlags pg i, leafKey pg i, leafValue pg i) ∈ E := by
    rw [← hE]; unfold treeEls
    exact List.mem_flatMap.2 ⟨pg, hmemL, List.mem_map.2 ⟨i, List.mem_range.2 hix, rfl⟩⟩
  obtain ⟨h1, ⟨h2, h2'⟩, h3⟩ := hel _ hmem
  obtain ⟨-, -, -, -, -, hfl, hpt, -⟩ :=
    leavesF_page P hwm _ root lo hi hs.wf hs.keys pg hmemL
  cases hpt with
  | branch _ _ hb _ _ => rw [hfl] at hb; cases hb
  | leaf _ _ _ hwf _ =>
    have hb := (hwf.2.2.1 i hix).1
    have hk : (leafKey pg i).length = leafKsize pg i := by
      unfold leafKey bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega
    have hv : (leafValue pg i).length = leafVsize pg i := by
      unfold leafValue bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega
    simp only at h1 h2 h2' h3
    refine ⟨h1, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← hk]; exact h2
    · rw [← hk]; exact h2'
    · rw [← hk, ← hv]; exact h3
    · have hn := hnest (leafFlags pg i, leafKey pg i, leafValue pg i) hmem
      intro bpg hbpg j hj
      exact hn bpg hbpg j hj

end shape

end Spill

end bbolt
end EtcdGrove
end Perennial
