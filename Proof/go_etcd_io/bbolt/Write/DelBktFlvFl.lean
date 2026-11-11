/-
U7q (`notes/bbolt-proof-plan.md`): **the writer's freelist after `child.free()`'s frees**
(`FLPg.freeAll` of extents it can free in order), for `Write/DelBktFlv.dbk_flView`: the pending
slots are the old ones and the extents' slots (`pendSlots_freeAll`); the MVCC rule of a view whose
pages the extents are, and older than the writer, kept (`mvccView_freeAll`); the ids distinct and
below `2^62` (`allIds_freeAll_ok`); the pending entries aligned (`pendAligned_freeAll`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktFreeFl
public import Proof.go_etcd_io.bbolt.Write.Free
public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section flfl
variable [GooseExts]

/-- A slot of a run, as a number (no wrap-around). -/
theorem mem_runIds_map (id : w64) (n s : Nat) (h : id.toNat + n < 2 ^ 64) :
    s ∈ (runIds id n).map BitVec.toNat ↔ id.toNat ≤ s ∧ s < id.toNat + n := by
  constructor
  · intro hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    exact (mem_runIds (id := id) (n := n) (by omega)).1 hx
  · intro hs
    refine List.mem_map.2 ⟨W64 (s : Int), (mem_runIds (id := id) (n := n) (by omega)).2 ?_, ?_⟩
    · unfold inRun; simp only [W64, BitVec.toNat_ofInt]; omega
    · simp only [W64, BitVec.toNat_ofInt]; omega

/-- **The pending slots after the frees**: the old ones and the extents'. -/
theorem pendSlots_freeAll (txid : w64) (s : Nat) : ∀ (es : List (w64 × Nat)) (fl : FLPg),
    fl.canFreeAll txid es →
    (s ∈ pendSlots (fl.freeAll txid es) ↔
      s ∈ pendSlots fl ∨ ∃ e ∈ es, e.1.toNat ≤ s ∧ s < e.1.toNat + e.2)
  | [], fl, _ => by simp [FLPg.freeAll]
  | e :: es, fl, h => by
    obtain ⟨h1, h2⟩ := h
    rw [freeAll_cons, pendSlots_freeAll txid s es _ h2]
    have hp : s ∈ pendSlots (fl.freePages txid e.1 e.2) ↔
        s ∈ pendSlots fl ∨ (e.1.toNat ≤ s ∧ s < e.1.toNat + e.2) := by
      unfold pendSlots
      rw [((pendingIds_freePages fl txid e.1 e.2).map BitVec.toNat).mem_iff, List.map_append,
        List.mem_append, mem_runIds_map e.1 e.2 s h1.2.1]
    rw [hp]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc

theorem pendAligned_freePages (fl : FLPg) (txid id : w64) (n : Nat) (h : pendAligned fl) :
    pendAligned (fl.freePages txid id n) := by
  intro t p hp
  simp only [FLPg.freePages, GMap.lookup_insert_eq_iff] at hp
  split at hp
  · rename_i htx
    subst htx
    cases hp
    simp only [List.length_append, runIds_length, List.length_replicate]
    rcases hq : fl.pending !! txid with _ | q
    · simp
    · simp only [Option.getD_some]; rw [h txid q hq]
  · exact h t p hp

theorem pendAligned_freeAll (txid : w64) : ∀ (es : List (w64 × Nat)) (fl : FLPg),
    pendAligned fl → pendAligned (fl.freeAll txid es)
  | [], _, h => h
  | e :: es, fl, h => by
    rw [freeAll_cons]; exact pendAligned_freeAll txid es _ (pendAligned_freePages fl txid _ _ h)

/-- **The MVCC rule kept across the frees** of extents of the view's pages, by a newer writer. -/
theorem mvccView_freeAll (v : View) (txid : w64) (ht : v.txid < txid.toNat)
    (hlt : ∀ s, coversSlot v.pages s → s < 2 ^ 64) : ∀ (es : List (w64 × Nat)) (fl : FLPg),
    fl.canFreeAll txid es → pendAligned fl →
    (∀ e ∈ es, ∃ pg, v.pages !! e.1.toNat = some pg ∧ 1 + pageOverflow pg = e.2) →
    mvccView fl v → mvccView (fl.freeAll txid es) v
  | [], _, _, _, _, h => h
  | e :: es, fl, hc, ha, he, h => by
    rw [freeAll_cons]
    exact mvccView_freeAll v txid ht hlt es _ hc.2 (pendAligned_freePages fl txid _ _ ha)
      (fun e' h' => he e' (List.mem_cons_of_mem _ h'))
      (mvccView_free fl v txid e.1 e.2 h ht hc.1 (Or.inl (he e (List.mem_cons_self ..))) hlt ha)

/-- **The ids distinct and below `2^62` after the frees** of extents below `2^62`. -/
theorem allIds_freeAll_ok (txid : w64) : ∀ (es : List (w64 × Nat)) (fl : FLPg),
    fl.canFreeAll txid es → (∀ e ∈ es, e.1.toNat + e.2 ≤ 2 ^ 62) →
    fl.allIds.Nodup → (∀ id ∈ fl.allIds, id.toNat < 2 ^ 62) →
    (fl.freeAll txid es).allIds.Nodup ∧ ∀ id ∈ (fl.freeAll txid es).allIds, id.toNat < 2 ^ 62
  | [], _, _, _, h1, h2 => ⟨h1, h2⟩
  | e :: es, fl, hc, hb, h1, h2 => by
    rw [freeAll_cons]
    obtain ⟨⟨_, hlt, hdis, _, _⟩, hc2⟩ := hc
    have hbe := hb e (List.mem_cons_self ..)
    have hp := allIds_freePages_perm fl txid e.1 e.2
    refine allIds_freeAll_ok txid es _ hc2 (fun e' h' => hb e' (List.mem_cons_of_mem _ h')) ?_ ?_
    · refine hp.nodup_iff.2 (List.nodup_append.2 ⟨h1, runIds_nodup (by omega), ?_⟩)
      rintro a ha b hb' rfl
      exact hdis a hb' ha
    · intro x hx
      rcases List.mem_append.1 (hp.mem_iff.1 hx) with h | h
      · exact h2 x h
      · have := (mem_runIds (id := e.1) (n := e.2) (by omega)).1 h
        unfold inRun at this; omega

end flfl

end Write

end bbolt
end EtcdGrove
end Perennial
