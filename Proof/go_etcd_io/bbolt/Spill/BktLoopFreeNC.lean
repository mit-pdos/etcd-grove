/-
`Bucket.spill`'s root loop (U9x3, `notes/bbolt-proof-plan.md`): **the free ids and the committed
tree's slots** (the coordinator's two new `spPre` clauses, for each `node.spill` call). The free
ids cover no committed page (`wdbOK`'s 5th clause, `x.toNat ∉ treeSlots w.C`), and the steps only
shrink the free list (`alloc` filters it, `freePages` adds pending ids only); the committed tree's
slots lie below its high-water mark (`treeOK`), hence below any mark at least it.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSlot
public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section freenc
variable [GooseExts]

/-- **The steps only shrink the free list.** -/
theorem free_applySteps_sub (fl : FLPg) (txid : w64) (st : List FLStep) :
    ∀ y ∈ (fl.applySteps txid st).free, y ∈ fl.free := by
  induction st generalizing fl with
  | nil => intro y hy; exact hy
  | cons s st ih =>
    intro y hy
    unfold FLPg.applySteps at hy
    rw [List.foldl_cons] at hy
    have h := ih _ y hy
    cases s with
    | free id n => exact h
    | alloc id n => exact (List.mem_filter.1 h).1

/-- **The free ids cover no committed page** (`wdbOK`'s 5th clause). -/
theorem freeNoCov_of_wdbOK {w : WDb} (h : wdbOK w) :
    ∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat :=
  fun y hy hc => h.2.2.2.2.1 y hy (mem_pagesSlots_cov.2 hc)

/-- **The free ids cover no committed page, after the steps.** -/
theorem freeNoCov_steps {P : Pages} {fl : FLPg} (h : ∀ y ∈ fl.free, ¬ coversSlot P y.toNat)
    (txid : w64) (st : List FLStep) :
    ∀ y ∈ (fl.applySteps txid st).free, ¬ coversSlot P y.toNat :=
  fun y hy => h y (free_applySteps_sub fl txid st y hy)

/-- **The committed tree's slots lie below any mark at least its high-water mark.** -/
theorem treeSlots_lt {C : CommitSt} (hc : treeOK C) {m : Nat} (hm : C.hwm ≤ m) :
    ∀ s ∈ treeSlots C, s < m := by
  intro s hs
  obtain ⟨id, pg, hpg, -, h2⟩ := mem_pagesSlots_cov.1 hs
  have := hc.2.2.2.1 id pg hpg
  omega

end freenc

end Spill

end bbolt
end EtcdGrove
end Perennial
