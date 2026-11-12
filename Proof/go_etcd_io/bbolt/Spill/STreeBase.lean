/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 5: **what the spill keeps of
the base tree**: in a `treeOK` committed state (the writer's base view), the subtree of any of its
pages is an `sTree` (its keys within the bounds the caller knows, its height the base's height
function's), with its pages `subPages`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeMono

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Spill

section base
variable [GooseExts]

open Classical in
/-- The pages of the tree from `id` in `P`. -/
def subPages (P : Pages) (id : Nat) : List Nat :=
  P.domList.filter fun x => decide (treeHas P id x)

theorem mem_subPages {P : Pages} {id x : Nat} : x ∈ subPages P id ↔ treeHas P id x := by
  unfold subPages
  rw [List.mem_filter, GMap.mem_dom_list]
  constructor
  · intro h; simpa using h.2
  · intro h
    obtain ⟨pg, hpg⟩ := treeHas_page h
    exact ⟨by rw [hpg]; rfl, by simpa using h⟩

theorem subPages_nodup (P : Pages) (id : Nat) : (subPages P id).Nodup :=
  (GMap.nodup_dom_list P).sublist (List.filter_sublist)

/-- **A subtree of a `treeOK` tree** is an `sTree`. -/
theorem sTree_base (C : CommitSt) (hok : treeOK C) {id : Nat} (ht : treeHas C.pages C.root id)
    {lo hi : Option (List w8)} (hk : treeKeys C.pages id lo hi) (pht : Nat → Nat)
    (hpht : pageHts C.pages pht) :
    sTree C.pages C.hwm id lo hi (pht id) (subPages C.pages id) := by
  obtain ⟨⟨hwf, ⟨hgood, hu⟩, -, -⟩, -, hdisj, hext, -, -⟩ := hok
  refine ⟨Read.treeHas_treeWF _ _ ht hwf, hk, fun x => mem_subPages.symm,
    subPages_nodup _ _, fun x _ pg hp => hgood x pg hp, fun x _ pg hp => ?_,
    ⟨pht, fun x _ pg hp => hpht x pg hp, rfl⟩,
    fun x _ y _ hne pgx pgy hpx hpy => hdisj x pgx y pgy hpx hpy hne,
    fun x _ pg hp => hext x pg hp⟩
  exact ⟨fun hb => hu.1 x pg hp hb, fun hl => hu.2 x pg hp hl⟩

end base

end Spill

end bbolt
end EtcdGrove
end Perennial
