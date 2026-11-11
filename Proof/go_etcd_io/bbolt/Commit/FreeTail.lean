/-
**The spill's facts across `Commit`'s free of the synced freelist page** (U10n): after the free
(`w.freeFl f n`, the page's run `[f, f + n)` pending for the writer) the tail takes the spill's
post (`spillOK`, `spillBufs`, the new tree's slots not pending) over the freed writer side. The
free is one more freelist step of the writer (`spillOK_freeFl`); the dirty pages and the new tree
stay off the run given that no dirty page lies in it (`hbx`), and the committed tree does not
cover it (`flCurOK`'s slot clause).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.PubPre
public import Proof.go_etcd_io.bbolt.Commit.FreeFlPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

omit [GooseExts] in
theorem ft_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- A free keeps the pending slots. -/
theorem ft_pendSlots_mono (fl : FLPg) (T id : w64) (n : Nat) {y : Nat}
    (hy : y ∈ pendSlots fl) : y ∈ pendSlots (fl.freePages T id n) := by
  unfold pendSlots at hy ⊢
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  exact List.mem_map_of_mem ((pendingIds_freePages_perm fl T id n).mem_iff.2
    (List.mem_append_left _ hz))

/-- **`spillOK` after the free**: the free is one more step of the writer's freelist. -/
theorem spillOK_freeFl (X1 X2 : WX) (C : CommitSt) (fl1 : FLPg) (w2 : WDb) (txid : w64) (f n : Nat)
    (htx : w2.wtxid = txid) (h : spillOK X1 X2 C fl1 w2.fl txid) :
    spillOK X1 X2 C fl1 (w2.freeFl f n).fl txid := by
  obtain ⟨a1, a2, a3, a4, a5, ⟨st, hst, hs⟩, a7⟩ := h
  refine ⟨a1, a2, a3, a4, fun s h1 h2 => ft_pendSlots_mono _ _ _ _ (a5 s h1 h2),
    ⟨st ++ [FLStep.free (W64 (f : Int)) n], ?_, fun s hm => ?_⟩, a7⟩
  · rw [WDb.freeFl.proj_fl, hst, htx]
    unfold FLPg.applySteps
    rw [List.foldl_append]
    rfl
  · rcases hs s hm with h | ⟨id, k, hmem, hk⟩ | h
    · exact .inl h
    · exact .inr (.inl ⟨id, k, List.mem_append_left _ hmem, hk⟩)
    · exact .inr (.inr h)

/-- **`spillBufs` after the free**, given that no dirty page lies in the freed run. -/
theorem spillBufs_freeFl (X2 : WX) (C : CommitSt) (w2 : WDb) (f n : Nat) (hn : f + n < 2 ^ 64)
    (hbx : ∀ s ∈ bufSlots X2.t.bufs, ¬ (f ≤ s ∧ s < f + n))
    (h : spillBufs X2 C w2.fl) : spillBufs X2 C (w2.freeFl f n).fl := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun id pg hp => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := h2 id pg hp
  refine ⟨c1, c2, c3, c4, fun j hj => ?_⟩
  obtain ⟨d1, d2, d3, d4⟩ := c5 j hj
  refine ⟨d1, ?_, ?_, d4⟩
  · rw [WDb.freeFl.proj_fl, pendSlots_freePages _ _ _ _ (by rw [ft_W64_toNat f (by omega)]; exact hn)]
    rintro (hm | hm)
    · exact d2 hm
    · rw [ft_W64_toNat f (by omega)] at hm
      exact hbx _ ((mem_bufSlots _ _).2 ⟨id, pg, hp, by omega, by omega⟩) hm
  · exact d3

/-- **The new tree off the freed run**: its pages are the committed ones (which do not cover the
run) or dirty pages (none in the run). -/
theorem spill_tree_off_run (X1 X2 : WX) (C : CommitSt) (fl1 fl2 : FLPg) (txid : w64) (f n : Nat)
    (hsp : spillOK X1 X2 C fl1 fl2 txid)
    (hcov : ∀ s, f ≤ s → s < f + n → ¬ coversSlot C.pages s)
    (hbx : ∀ s ∈ bufSlots X2.t.bufs, ¬ (f ≤ s ∧ s < f + n)) :
    ∀ s ∈ treeSlots (spillC X2 C.pages), ¬ (f ≤ s ∧ s < f + n) := by
  obtain ⟨htree, -, -, -, -, -, hpages⟩ := hsp
  intro s hs hr
  obtain ⟨id, pg, hp, h1, h2⟩ := (pp_mem_pagesSlots _ _).1 hs
  have hext := htree.2.2.2.1 id pg hp
  have hlt : id < 2 ^ 64 := by
    have : (spillC X2 C.pages).hwm = X2.t.mv.pgid'.toNat := rfl
    have := X2.t.mv.pgid'.isLt
    omega
  rcases hpages id pg hp with h | h
  · exact hcov s hr.1 hr.2 ((mem_pagesSlots_iff _ _).1 ((pp_mem_pagesSlots _ _).2 ⟨id, pg, h, h1, h2⟩))
  · exact hbx s ((mem_bufSlots _ _).2 ⟨_, pg, h, by rw [ft_W64_toNat id hlt]; omega,
      by rw [ft_W64_toNat id hlt]; omega⟩) hr

/-- **The new tree's slots not pending after the free.** -/
theorem treeNP_freeFl (P : List Nat) (w2 : WDb) (f n : Nat) (hn : f + n < 2 ^ 64)
    (hnp : ∀ s ∈ P, s ∉ pendSlots w2.fl) (hoff : ∀ s ∈ P, ¬ (f ≤ s ∧ s < f + n)) :
    ∀ s ∈ P, s ∉ pendSlots (w2.freeFl f n).fl := by
  intro s hs
  rw [WDb.freeFl.proj_fl, pendSlots_freePages _ _ _ _ (by rw [ft_W64_toNat f (by omega)]; exact hn)]
  rintro (hm | hm)
  · exact hnp s hs hm
  · rw [ft_W64_toNat f (by omega)] at hm
    exact hoff s hs hm

end pure

end bbolt
end EtcdGrove
end Perennial
