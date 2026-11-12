/-
U7p (`notes/bbolt-proof-plan.md`): **freeing a list of extents** (`canFreeAll_of_disj`, for
`DeleteBucket`'s `child.free()`, `Write/DelBktFree`): extents above the metas, below `2^62`, whose
first pages the writer did not allocate, can be freed in order when their ids and the freelist's
are distinct and below `2^62` (each `Free` adds its run to the pending ids and drops its allocation
record, so the next extent's conditions stay).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureFree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section fl
variable [GooseExts]

/-- The ids of extents. -/
def extIds (es : List (w64 × Nat)) : List w64 := es.flatMap fun e => runIds e.1 e.2

theorem allIds_freePages_perm (fl : FLPg) (txid id : w64) (n : Nat) :
    (fl.freePages txid id n).allIds.Perm (fl.allIds ++ runIds id n) := by
  unfold FLPg.allIds
  have hf : (fl.freePages txid id n).free = fl.free := rfl
  rw [hf, List.append_assoc]
  exact (pendingIds_freePages fl txid id n).append_left _

/-- **Extents with distinct ids, none the freelist's, can be freed in order.** -/
theorem canFreeAll_of_disj (txid : w64) (htx0 : txid ≠ W64 0) :
    ∀ (es : List (w64 × Nat)) (fl : FLPg),
      (∀ e ∈ es, 2 ≤ e.1.toNat ∧ e.1.toNat + e.2 ≤ 2 ^ 62 ∧ (fl.allocs !! e.1).getD 0 ≠ txid) →
      (fl.allIds ++ extIds es).Nodup →
      (∀ x ∈ fl.allIds ++ extIds es, x.toNat < 2 ^ 62) →
      fl.canFreeAll txid es
  | [], _, _, _, _ => trivial
  | e :: es, fl, he, hnd, hlt => by
    obtain ⟨h2, hb, ha⟩ := he e (List.mem_cons_self ..)
    have hx : extIds (e :: es) = runIds e.1 e.2 ++ extIds es := by
      unfold extIds; rw [List.flatMap_cons]
    rw [hx] at hnd hlt
    refine ⟨⟨h2, by omega, ?_, ha, ?_⟩, ?_⟩
    · intro x hx hxa
      exact (List.nodup_append.1 hnd).2.2 x hxa x (List.mem_append_left _ hx) rfl
    · have hlen := Spill.length_le_of_nodup_lt' _ (2 ^ 62) hnd hlt
      simp only [List.length_append, runIds, List.length_map, List.length_range] at hlen
      omega
    · have hp : ((fl.freePages txid e.1 e.2).allIds ++ extIds es).Perm
          (fl.allIds ++ (runIds e.1 e.2 ++ extIds es)) := by
        rw [← List.append_assoc]
        exact (allIds_freePages_perm fl txid e.1 e.2).append_right _
      refine canFreeAll_of_disj txid htx0 es _ ?_ (hp.nodup_iff.2 hnd)
        (fun x hx => hlt x (hp.mem_iff.1 hx))
      intro e' he'
      obtain ⟨a, b, c⟩ := he e' (List.mem_cons_of_mem _ he')
      refine ⟨a, b, ?_⟩
      show ((fl.allocs.delete e.1) !! e'.1).getD 0 ≠ txid
      rw [GMap.lookup_delete_iff]
      split
      · exact fun h => htx0 h.symm
      · exact c

end fl

end Write

end bbolt
end EtcdGrove
end Perennial
