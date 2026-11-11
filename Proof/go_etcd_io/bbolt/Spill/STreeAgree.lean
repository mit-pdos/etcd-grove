/-
The spill's pure tree facts (U9e, `notes/bbolt-proof-plan.md`): **an `sTree` in a map that agrees
on its pages** (`sTree_agree`), below a higher mark: the buffers the spill adds are at slots no
kept tree owns, so the kept trees are `sTree`s of the new page map (`sTree_mono` asks a larger
map, which a buffer over a dropped base page is not).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeBuild

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Spill

section agree
variable [GooseExts]

/-- **A well-formed tree of `P` has no more pages in a map that agrees on its pages.** -/
theorem treeHas_of_agree {P P' : Pages} (hwm : Nat) {root id : Nat}
    (h' : treeHas P' root id) : treeWF P hwm root →
      (∀ y, treeHas P root y → P' !! y = P !! y) → treeHas P root id :=
  treeHas.rec (pages := P')
    (motive_1 := fun root id _ => treeWF P hwm root →
      (∀ y, treeHas P root y → P' !! y = P !! y) → treeHas P root id)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len →
      (∀ y, pageHas P pg y → P' !! y = P !! y) → pageHas P pg id)
    (motive_3 := fun v id _ => bucketWF P hwm v →
      (∀ y, bucketHas P v y → P' !! y = P !! y) → bucketHas P v id)
    (fun root pg hpg hw _ => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ _ => exact treeHas.root root pg' hpg')
    (fun root pg id hpg _ ih hw ha => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        have e := ha root (treeHas.root root pg' hpg')
        rw [hpg, hpg'] at e; cases e
        exact treeHas.sub root pg id hpg'
          (ih _ hpt fun y hy => ha y (treeHas.sub root pg y hpg' hy)))
    (fun pg i id hfl hi _ ih len hpt ha => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      | branch _ _ _ _ hch =>
        exact pageHas.child pg i id hfl hi
          (ih (hch i hi) fun y hy => ha y (pageHas.child pg i y hfl hi hy)))
    (fun pg i id hfl hi hbf _ ih len hpt ha => by
      cases hpt with
      | leaf _ _ _ _ hb =>
        exact pageHas.bucket pg i id hfl hi hbf
          (ih (hb i hi hbf) fun y hy => ha y (pageHas.bucket pg i y hfl hi hbf hy))
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl')
    (fun v id hr _ ih hb ha => by
      cases hb with
      | file _ _ _ ht =>
        exact bucketHas.file v id hr (ih ht fun y hy => ha y (bucketHas.file v y hr hy))
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb ha => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ _ hpt =>
        exact bucketHas.inline v id hr (ih _ hpt fun y hy => ha y (bucketHas.inline v y hr hy)))
    h'

/-- `treeHas_of_agree` for a nested bucket's value. -/
theorem bucketHas_of_agree {P P' : Pages} (hwm : Nat) {v : List w8} {id : Nat}
    (h' : bucketHas P' v id) : bucketWF P hwm v →
      (∀ y, bucketHas P v y → P' !! y = P !! y) → bucketHas P v id :=
  bucketHas.rec (pages := P')
    (motive_1 := fun root id _ => treeWF P hwm root →
      (∀ y, treeHas P root y → P' !! y = P !! y) → treeHas P root id)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len →
      (∀ y, pageHas P pg y → P' !! y = P !! y) → pageHas P pg id)
    (motive_3 := fun v id _ => bucketWF P hwm v →
      (∀ y, bucketHas P v y → P' !! y = P !! y) → bucketHas P v id)
    (fun root pg hpg hw _ => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ _ => exact treeHas.root root pg' hpg')
    (fun root pg id hpg _ ih hw ha => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        have e := ha root (treeHas.root root pg' hpg')
        rw [hpg, hpg'] at e; cases e
        exact treeHas.sub root pg id hpg'
          (ih _ hpt fun y hy => ha y (treeHas.sub root pg y hpg' hy)))
    (fun pg i id hfl hi _ ih len hpt ha => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      | branch _ _ _ _ hch =>
        exact pageHas.child pg i id hfl hi
          (ih (hch i hi) fun y hy => ha y (pageHas.child pg i y hfl hi hy)))
    (fun pg i id hfl hi hbf _ ih len hpt ha => by
      cases hpt with
      | leaf _ _ _ _ hb =>
        exact pageHas.bucket pg i id hfl hi hbf
          (ih (hb i hi hbf) fun y hy => ha y (pageHas.bucket pg i y hfl hi hbf hy))
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl')
    (fun v id hr _ ih hb ha => by
      cases hb with
      | file _ _ _ ht =>
        exact bucketHas.file v id hr (ih ht fun y hy => ha y (bucketHas.file v y hr hy))
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb ha => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ _ hpt =>
        exact bucketHas.inline v id hr (ih _ hpt fun y hy => ha y (bucketHas.inline v y hr hy)))
    h'

/-- **An `sTree` in a map that agrees on its pages, below a higher mark.** -/
theorem sTree_agree {P P' : Pages} {hwm hwm' id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hagS : ∀ x ∈ S, P' !! x = P !! x) (hh : hwm ≤ hwm')
    (hs : sTree P hwm id lo hi h S) : sTree P' hwm' id lo hi h S := by
  have hag : ∀ y, treeHas P id y → P' !! y = P !! y := fun y hy => hagS y ((hs.has y).1 hy)
  have hS : ∀ x ∈ S, ∀ pg, P' !! x = some pg → P !! x = some pg := by
    intro x hx pg hp
    rw [← hagS x hx]; exact hp
  have hiff : ∀ x, treeHas P' id x ↔ treeHas P id x :=
    fun x => ⟨fun h' => treeHas_of_agree hwm h' hs.wf hag, treeHas_agree hag⟩
  refine ⟨treeWF_hwm hh (treeWF_agree hs.wf hag), treeKeys_agree hs.keys hag,
    fun x => (hiff x).trans (hs.has x), hs.nodup, fun x hx pg hp => hs.good x hx pg (hS x hx pg hp),
    fun x hx pg hp => ?_, ?_, fun x hx y hy hne pgx pgy hpx hpy =>
      hs.disj x hx y hy hne pgx pgy (hS x hx pgx hpx) (hS y hy pgy hpy),
    fun x hx pg hp => by have := hs.ext x hx pg (hS x hx pg hp); omega⟩
  · have hp' := hS x hx pg hp
    have hxt : treeHas P id x := (hs.has x).2 hx
    have hwx : treeWF P hwm x := Read.treeHas_treeWF P hwm hxt hs.wf
    refine uniqAt_congr (fun i hi hb d => ⟨fun h' => ?_, treeHas_agree ?_⟩)
      (fun i hi hl hbf d => ⟨fun h' => ?_, bucketHas_agree ?_⟩) (hs.uniq x hx pg hp')
    · exact treeHas_of_agree hwm h' (treeWF_branch_child hwx hp' hb hi)
        fun y hy => hag y (treeHas_trans hxt (treeHas_child hp' hb hi hy))
    · exact fun y hy => hag y (treeHas_trans hxt (treeHas_child hp' hb hi hy))
    · exact bucketHas_of_agree hwm h' (treeWF_leaf_bucketWF hwx hp' hl hi hbf)
        fun y hy => hag y (treeHas_trans hxt (treeHas_bucket hp' hl hi hbf hy))
    · exact fun y hy => hag y (treeHas_trans hxt (treeHas_bucket hp' hl hi hbf hy))
  · obtain ⟨pht, hpht, hid⟩ := hs.hts
    exact ⟨pht, fun x hx pg hp => hpht x hx pg (hS x hx pg hp), hid⟩

/-- `sTree_agree` for a nested bucket's value. -/
theorem bvalS_agree {P P' : Pages} {hwm hwm' : Nat} {v : List w8} {S : List Nat}
    (hagS : ∀ x ∈ S, P' !! x = P !! x) (hh : hwm ≤ hwm') (hb : bvalS P hwm v S) :
    bvalS P' hwm' v S := by
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with h | ⟨hr, ht, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr, ht, sTree_agree hagS hh hs⟩

end agree

end Spill

end bbolt
end EtcdGrove
end Perennial
