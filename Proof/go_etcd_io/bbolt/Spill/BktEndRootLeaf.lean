/-
`Bucket.spill`'s root loop's end (U9x6, `notes/bbolt-proof-plan.md`): **a leaf with a bucket entry
below the committed root is one of the root's own leaves** (`ownHas_of_bktLeaf`). In the committed
tree (`treeOK`), the nested buckets' leaves are plain (`rootShape`), so a page reached through a
nested bucket's value holds no bucket entry: a leaf page with one, under an own page of the
committed root, is reached through branches only. (No fact ties the root bucket's header to the
committed root; this replaces it, for `Spill/BktEndNil`.)
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov
public import Proof.go_etcd_io.bbolt.Spill.BktRootKeys

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section rootLeaf
variable [GooseExts]

/-- A leaf page holding a bucket entry. -/
def bktEntPg (P : Pages) (x : Nat) : Prop :=
  ∃ pg, P !! x = some pg ∧ pageFlags pg = leafPageFlag ∧
    ∃ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag

/-- **A bucket whose leaves are plain reaches no page with a bucket entry.** -/
theorem bucketHas_noBkt {P : Pages} {hwm : Nat} {v : List w8} (hwf : bucketWF P hwm v)
    (hpl : ∀ bpg, bktLeafPg P v bpg → ∀ j < pageCount bpg, leafFlags bpg j % 2 = 0)
    {x : Nat} (hx : bucketHas P v x) (hb : bktEntPg P x) : False := by
  obtain ⟨pg, hpg, hl, i, hi, hbi⟩ := hb
  cases hx with
  | file _ _ h0 ht =>
    have hpl' : ∀ p pg', ownHas P (inBucketRoot v) p → P !! p = some pg' →
        pageFlags pg' = leafPageFlag → ∀ i < pageCount pg', leafFlags pg' i % 2 ≠ bucketLeafFlag := by
      intro p pg' ho hp hl' j hj he
      have := hpl pg' (Or.inr ⟨h0, p, ho, hp, hl'⟩) j hj
      rw [this] at he; unfold bucketLeafFlag at he; omega
    have ho := ownHas_of_treeHas hpl' ht
    exact hpl' x pg ho hpg hl i hi hbi
  | inline _ _ h0 hph =>
    have hipl := hpl (inlinePage v) (Or.inl ⟨h0, rfl⟩)
    cases hph with
    | child _ j _ hfl _ _ =>
      cases hwf with
      | file _ _ h0' _ => exact h0' h0
      | inline _ _ _ hfl' _ =>
        rw [hfl] at hfl'; exact absurd hfl' (by unfold branchPageFlag leafPageFlag; decide)
    | bucket _ j _ _ hj hbf _ =>
      have := hipl j hj
      rw [this] at hbf; unfold bucketLeafFlag at hbf; omega

/-- A bucket entry of a well-formed leaf has a well-formed value. -/
theorem bucketWF_of_leaf {P : Pages} {hwm a : Nat} {pg : List w8} (hw : treeWF P hwm a)
    (hpa : P !! a = some pg) (hl : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) : bucketWF P hwm (leafValue pg i) := by
  rcases hw with ⟨_, pg', _, _, hpg', _, _, hpt⟩
  rw [hpa] at hpg'; cases hpg'
  cases hpt with
  | leaf _ _ _ _ hb => exact hb i hi hbf
  | branch _ _ hf _ _ =>
    rw [hl] at hf; exact absurd hf (by unfold branchPageFlag leafPageFlag; decide)

/-- Own pages compose. -/
theorem ownHas_trans {P : Pages} {a b c : Nat} (h1 : ownHas P a b) (h2 : ownHas P b c) :
    ownHas P a c := by
  induction h1 with
  | root => exact h2
  | child r pg i id hpg hf hi _ ih => exact ownHas.child r pg i c hpg hf hi (ih h2)

/-- **A leaf with a bucket entry below an own page of the committed root is an own page of it**
(see the module doc). -/
theorem ownHas_of_bktLeaf {C : CommitSt} (hcok : treeOK C) {a x : Nat}
    (ha : ownHas C.pages C.root a) (h : treeHas C.pages a x) (hb : bktEntPg C.pages x) :
    ownHas C.pages C.root x := by
  have hwf : treeWF C.pages C.hwm C.root := hcok.1.1
  have hrs : rootShape C.pages C.root := hcok.2.2.2.2.1
  exact treeHas.rec (pages := C.pages)
    (motive_1 := fun a b _ => (∀ p, ownHas C.pages a p → ownHas C.pages C.root p) →
      bktEntPg C.pages b → ownHas C.pages C.root b)
    (motive_2 := fun pg b _ => ∀ a, C.pages !! a = some pg →
      (∀ p, ownHas C.pages a p → ownHas C.pages C.root p) →
      bktEntPg C.pages b → ownHas C.pages C.root b)
    (motive_3 := fun _ _ _ => True)
    (fun a pg hpg hA _ => hA a (ownHas.root a pg hpg))
    (fun a _ _ hpg _ ih hA hb => ih a hpg hA hb)
    (fun pg i _ hfl hi _ ih a hpa hA hb =>
      ih (fun p hp => hA p (ownHas.child a pg i p hpa hfl hi hp)) hb)
    (fun pg i id hfl hi hbf hbh _ a hpa hA hb => by
      have hown := hA a (ownHas.root a pg hpa)
      have hw := treeWF_ownHas hown hwf
      have hvw := bucketWF_of_leaf hw hpa hfl hi hbf
      have hpl := fun bpg hbpg j hj => ((hrs a pg hown hpa hfl i hi).2.2.2 bpg hbpg j hj).1
      exact (bucketHas_noBkt hvw hpl hbh hb).elim)
    (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial)
    h (fun p hp => ownHas_trans ha hp) hb

end rootLeaf

end Spill

end bbolt
end EtcdGrove
end Perennial
