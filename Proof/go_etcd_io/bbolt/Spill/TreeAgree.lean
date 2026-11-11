/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 1: the tree predicates of
`Model/Tree` (`treeHas`, `treeWF`, `treeKeys`, `ownHas`) depend only on the pages of the tree.
A tree of `P` is the same tree of a page map `P'` that agrees with `P` on the tree's pages: a
larger map (the spill's written buffers over the base pages, `bufPages ∪ base`), or the tree's
own pages (`treePages`, `spillC`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Tree

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

/-- `P'` holds every page of `P`. -/
def pagesLe (P P' : Pages) : Prop := ∀ id pg, P !! id = some pg → P' !! id = some pg

theorem pagesLe_refl (P : Pages) : pagesLe P P := fun _ _ h => h

theorem pagesLe_trans {P1 P2 P3 : Pages} (h1 : pagesLe P1 P2) (h2 : pagesLe P2 P3) :
    pagesLe P1 P3 := fun id pg h => h2 id pg (h1 id pg h)

/-- **A tree's pages are a larger map's tree's.** -/
theorem treeHas_le {P P' : Pages} (hle : pagesLe P P') {root id : Nat} (h : treeHas P root id) :
    treeHas P' root id :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeHas P' root id)
    (motive_2 := fun pg id _ => pageHas P' pg id)
    (motive_3 := fun v id _ => bucketHas P' v id)
    (fun root pg hpg => treeHas.root root pg (hle _ _ hpg))
    (fun root pg id hpg _ ih => treeHas.sub root pg id (hle _ _ hpg) ih)
    (fun pg i id hfl hi _ ih => pageHas.child pg i id hfl hi ih)
    (fun pg i id hfl hi hbf _ ih => pageHas.bucket pg i id hfl hi hbf ih)
    (fun v id hr _ ih => bucketHas.file v id hr ih)
    (fun v id hr _ ih => bucketHas.inline v id hr ih)
    h

/-- **A well-formed tree of `P` has no more pages in a larger map.** -/
theorem treeHas_of_le {P P' : Pages} (hle : pagesLe P P') (hwm : Nat) {root id : Nat}
    (h : treeHas P' root id) : treeWF P hwm root → treeHas P root id :=
  treeHas.rec (pages := P')
    (motive_1 := fun root id _ => treeWF P hwm root → treeHas P root id)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → pageHas P pg id)
    (motive_3 := fun v id _ => bucketWF P hwm v → bucketHas P v id)
    (fun root pg hpg hw => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ _ => exact treeHas.root root pg' hpg')
    (fun root pg id hpg _ ih hw => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        have e := hle _ _ hpg'
        rw [hpg] at e; cases e
        exact treeHas.sub root pg id hpg' (ih _ hpt))
    (fun pg i id hfl hi _ ih len hpt => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      | branch _ _ _ _ hch => exact pageHas.child pg i id hfl hi (ih (hch i hi)))
    (fun pg i id hfl hi hbf _ ih len hpt => by
      cases hpt with
      | leaf _ _ _ _ hb => exact pageHas.bucket pg i id hfl hi hbf (ih (hb i hi hbf))
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl')
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ _ ht => exact bucketHas.file v id hr (ih ht)
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ _ hpt => exact bucketHas.inline v id hr (ih _ hpt))
    h

/-- `P'` agrees with `P` on the pages of the tree from `root`. -/
def agreeOn (P P' : Pages) (root : Nat) : Prop := ∀ id, treeHas P root id → P' !! id = P !! id

/-- **A well-formed tree is well-formed in a map that agrees on its pages.** -/
theorem treeWF_agree {P P' : Pages} {hwm root : Nat} (hw : treeWF P hwm root) :
    (∀ id, treeHas P root id → P' !! id = P !! id) → treeWF P' hwm root :=
  treeWF.rec (pages := P) (hwm := hwm)
    (motive_1 := fun root _ => (∀ id, treeHas P root id → P' !! id = P !! id) →
      treeWF P' hwm root)
    (motive_2 := fun pg len _ => (∀ id, pageHas P pg id → P' !! id = P !! id) →
      pageTreeWF P' hwm pg len)
    (motive_3 := fun v _ => (∀ id, bucketHas P v id → P' !! id = P !! id) → bucketWF P' hwm v)
    (fun root pg h2 hlt hpg hid hlen _ ih ha => by
      have e := ha root (treeHas.root root pg hpg)
      rw [hpg] at e
      exact treeWF.page root pg h2 hlt e hid hlen
        (ih fun id hp => ha id (treeHas.sub root pg id hpg hp)))
    (fun pg len hfl hlw _ ih ha => pageTreeWF.leaf pg len hfl hlw fun i hi hbf =>
      ih i hi hbf fun id hb => ha id (pageHas.bucket pg i id hfl hi hbf hb))
    (fun pg len hfl hbw _ ih ha => pageTreeWF.branch pg len hfl hbw fun i hi =>
      ih i hi fun id ht => ha id (pageHas.child pg i id hfl hi ht))
    (fun v h16 hr _ ih ha => bucketWF.file v h16 hr (ih fun id ht => ha id (bucketHas.file v id hr ht)))
    (fun v h16 hr hfl _ ih ha => bucketWF.inline v h16 hr hfl
      (ih fun id hp => ha id (bucketHas.inline v id hr hp)))
    hw

/-- **A tree's keys are the same in a map that agrees on its pages.** -/
theorem treeKeys_agree {P P' : Pages} {root : Nat} {lo hi : Option (List w8)}
    (hk : treeKeys P root lo hi) :
    (∀ id, treeHas P root id → P' !! id = P !! id) → treeKeys P' root lo hi := by
  induction hk with
  | leaf root pg lo hi hpg hfl hkin _ ih =>
    intro ha
    have e := ha root (treeHas.root root pg hpg)
    rw [hpg] at e
    refine treeKeys.leaf root pg lo hi e hfl hkin fun i hi hbf hr => ih i hi hbf hr fun id ht => ?_
    exact ha id (treeHas.sub root pg id hpg (pageHas.bucket pg i id hfl hi hbf
      (bucketHas.file _ id hr ht)))
  | branch root pg lo hi kind hpg hfl h2 hkin hch _ ih =>
    intro ha
    have e := ha root (treeHas.root root pg hpg)
    rw [hpg] at e
    refine treeKeys.branch root pg lo hi kind e hfl h2 hkin (fun i hi => ?_) (fun i hi => ?_)
    · obtain ⟨cpg, hc, h0, hk, hkey⟩ := hch i hi
      refine ⟨cpg, ?_, h0, hk, hkey⟩
      rw [ha _ (treeHas.sub root pg _ hpg (pageHas.child pg i _ hfl hi
        (treeHas.root _ cpg hc)))]
      exact hc
    · exact ih i hi fun id ht => ha id (treeHas.sub root pg id hpg (pageHas.child pg i id hfl hi ht))

/-- **A tree's pages are the same in a map that agrees on its pages** (both directions). -/
theorem treeHas_agree {P P' : Pages} {root id : Nat}
    (ha : ∀ id, treeHas P root id → P' !! id = P !! id) (h : treeHas P root id) :
    treeHas P' root id := by
  have key : ∀ {r x}, treeHas P r x → (∀ y, treeHas P r y → P' !! y = P !! y) → treeHas P' r x :=
    fun {r x} h =>
    treeHas.rec (pages := P)
      (motive_1 := fun r x _ => (∀ y, treeHas P r y → P' !! y = P !! y) → treeHas P' r x)
      (motive_2 := fun pg x _ => (∀ y, pageHas P pg y → P' !! y = P !! y) → pageHas P' pg x)
      (motive_3 := fun v x _ => (∀ y, bucketHas P v y → P' !! y = P !! y) → bucketHas P' v x)
      (fun r pg hpg ha => by
        have e := ha r (treeHas.root r pg hpg); rw [hpg] at e
        exact treeHas.root r pg e)
      (fun r pg x hpg _ ih ha => by
        have e := ha r (treeHas.root r pg hpg); rw [hpg] at e
        exact treeHas.sub r pg x e (ih fun y hy => ha y (treeHas.sub r pg y hpg hy)))
      (fun pg i x hfl hi _ ih ha =>
        pageHas.child pg i x hfl hi (ih fun y hy => ha y (pageHas.child pg i y hfl hi hy)))
      (fun pg i x hfl hi hbf _ ih ha =>
        pageHas.bucket pg i x hfl hi hbf (ih fun y hy => ha y (pageHas.bucket pg i y hfl hi hbf hy)))
      (fun v x hr _ ih ha => bucketHas.file v x hr (ih fun y hy => ha y (bucketHas.file v y hr hy)))
      (fun v x hr _ ih ha =>
        bucketHas.inline v x hr (ih fun y hy => ha y (bucketHas.inline v y hr hy)))
      h
  exact key h ha

/-- `treeHas_le` for a nested bucket's value. -/
theorem bucketHas_le {P P' : Pages} (hle : pagesLe P P') {v : List w8} {id : Nat}
    (h : bucketHas P v id) : bucketHas P' v id :=
  bucketHas.rec (pages := P)
    (motive_1 := fun root id _ => treeHas P' root id)
    (motive_2 := fun pg id _ => pageHas P' pg id)
    (motive_3 := fun v id _ => bucketHas P' v id)
    (fun root pg hpg => treeHas.root root pg (hle _ _ hpg))
    (fun root pg id hpg _ ih => treeHas.sub root pg id (hle _ _ hpg) ih)
    (fun pg i id hfl hi _ ih => pageHas.child pg i id hfl hi ih)
    (fun pg i id hfl hi hbf _ ih => pageHas.bucket pg i id hfl hi hbf ih)
    (fun v id hr _ ih => bucketHas.file v id hr ih)
    (fun v id hr _ ih => bucketHas.inline v id hr ih)
    h

/-- `treeHas_of_le` for a nested bucket's value. -/
theorem bucketHas_of_le {P P' : Pages} (hle : pagesLe P P') (hwm : Nat) {v : List w8} {id : Nat}
    (h : bucketHas P' v id) : bucketWF P hwm v → bucketHas P v id :=
  bucketHas.rec (pages := P')
    (motive_1 := fun root id _ => treeWF P hwm root → treeHas P root id)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → pageHas P pg id)
    (motive_3 := fun v id _ => bucketWF P hwm v → bucketHas P v id)
    (fun root pg hpg hw => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ _ => exact treeHas.root root pg' hpg')
    (fun root pg id hpg _ ih hw => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        have e := hle _ _ hpg'
        rw [hpg] at e; cases e
        exact treeHas.sub root pg id hpg' (ih _ hpt))
    (fun pg i id hfl hi _ ih len hpt => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      | branch _ _ _ _ hch => exact pageHas.child pg i id hfl hi (ih (hch i hi)))
    (fun pg i id hfl hi hbf _ ih len hpt => by
      cases hpt with
      | leaf _ _ _ _ hb => exact pageHas.bucket pg i id hfl hi hbf (ih (hb i hi hbf))
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl')
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ _ ht => exact bucketHas.file v id hr (ih ht)
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ _ hpt => exact bucketHas.inline v id hr (ih _ hpt))
    h

/-- `treeHas_agree` for a nested bucket's value. -/
theorem bucketHas_agree {P P' : Pages} {v : List w8} {id : Nat}
    (ha : ∀ id, bucketHas P v id → P' !! id = P !! id) (h : bucketHas P v id) :
    bucketHas P' v id :=
  (bucketHas.rec (pages := P)
      (motive_1 := fun r x _ => (∀ y, treeHas P r y → P' !! y = P !! y) → treeHas P' r x)
      (motive_2 := fun pg x _ => (∀ y, pageHas P pg y → P' !! y = P !! y) → pageHas P' pg x)
      (motive_3 := fun v x _ => (∀ y, bucketHas P v y → P' !! y = P !! y) → bucketHas P' v x)
      (fun r pg hpg ha => by
        have e := ha r (treeHas.root r pg hpg); rw [hpg] at e
        exact treeHas.root r pg e)
      (fun r pg x hpg _ ih ha => by
        have e := ha r (treeHas.root r pg hpg); rw [hpg] at e
        exact treeHas.sub r pg x e (ih fun y hy => ha y (treeHas.sub r pg y hpg hy)))
      (fun pg i x hfl hi _ ih ha =>
        pageHas.child pg i x hfl hi (ih fun y hy => ha y (pageHas.child pg i y hfl hi hy)))
      (fun pg i x hfl hi hbf _ ih ha =>
        pageHas.bucket pg i x hfl hi hbf (ih fun y hy => ha y (pageHas.bucket pg i y hfl hi hbf hy)))
      (fun v x hr _ ih ha => bucketHas.file v x hr (ih fun y hy => ha y (bucketHas.file v y hr hy)))
      (fun v x hr _ ih ha =>
        bucketHas.inline v x hr (ih fun y hy => ha y (bucketHas.inline v y hr hy)))
      h) ha

end agree

end Spill

end bbolt
end EtcdGrove
end Perennial
