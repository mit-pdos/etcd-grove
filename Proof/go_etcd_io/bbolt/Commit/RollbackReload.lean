/-
`Tx.rollback`'s synced `Reload` branch (U10f of `notes/bbolt-proof-plan.md`): the freelist page's
id (`db.meta().Freelist()`, `wp_meta_Freelist`), its extent's cells out of `wCells` and read
against the page-cache bytes `wBytes` (`ext_agree`, by `cellsR_agree_bytes` slot by slot), back
(`ext_cells_back`); `Reload`'s premises from `flCurOK` (`reload_premises`), the store's
(`reload_store_ids`) and `wdbOK` after it (`wdbOK_reload_synced`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
set_option linter.unusedSectionVars false
variable [GooseExts]

/-- A list without repeats whose members are all in `W` is, with the rest, a permutation of `W`. -/
theorem perm_append_of_nodup_sub {A : Type} [DecidableEq A] (ws W : List A) (hn : ws.Nodup)
    (hsub : ∀ s ∈ ws, s ∈ W) : ∃ rest, W.Perm (ws ++ rest) := by
  obtain ⟨l, hl, hsl⟩ := List.subperm_of_subset hn hsub
  obtain ⟨r, hr⟩ := hsl.exists_perm_append
  exact ⟨r, hr.trans (hl.append_right r)⟩

/-- A committed-pending id is a pending id. -/
theorem committedPending_mem (fl : FLPg) (C : CommitSt) (x : w64) (h : committedPending fl C x) :
    x ∈ fl.pendingIds := by
  obtain ⟨t, pd, ht, hx, -⟩ := h
  unfold FLPg.pendingIds
  exact List.mem_flatMap.2 ⟨(t, pd), (GMap.mem_toList _ _ _).2 ht, hx⟩

theorem toNat_mem_pendSlots (fl : FLPg) (x : w64) (h : x ∈ fl.pendingIds) :
    x.toNat ∈ pendSlots fl :=
  List.mem_map_of_mem h

theorem mem_pendSlots_iff (fl : FLPg) (x : w64) : x.toNat ∈ pendSlots fl ↔ x ∈ fl.pendingIds := by
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    rw [BitVec.eq_of_toNat_eq e] at hy; exact hy
  · exact toNat_mem_pendSlots fl x

/-- Distinct ids in `[2, n)` number at most `n - 2`. -/
theorem length_le_of_nodup_two (l : List w64) (n : Nat) (h2 : 2 ≤ n) (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, 2 ≤ x.toNat ∧ x.toNat < n) : l.length + 2 ≤ n := by
  have h := length_le_of_nodup_lt (W64 0 :: W64 1 :: l) n ?_ ?_
  · simp only [List.length_cons] at h; omega
  · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hnd⟩⟩
    · intro hm
      rcases List.mem_cons.1 hm with e | hm
      · exact absurd e (by decide)
      · have := (hlt _ hm).1; simp at this
    · intro hm; have := (hlt _ hm).1; simp at this
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp; omega
    rcases List.mem_cons.1 hx with rfl | hx
    · simp; omega
    · exact (hlt x hx).2

/-- **The writer side's facts about the synced freelist page's ids** (`flCurOK` and `wdbOK`): each
is at least 2, below the high-water mark, and no store slot unless pending. -/
theorem flIds_facts (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    ∀ x ∈ flIds (extentBytes w.wb f), 2 ≤ x.toNat ∧ x.toNat < w.C.hwm ∧
      (x ∈ w.fl.pendingIds ∨ (x ∉ w.fl.pendingIds ∧ ¬ coversSlot w.C.pages x.toNat)) := by
  intro x hx
  obtain ⟨-, -, -, -, -, a6, -, -, -, -, a11, -⟩ := hok
  obtain ⟨-, -, -, -, -, -, b7, -, -, -, -, b12⟩ := a6 f hf f hf
  refine ⟨b7 x hx, ?_, ?_⟩
  · rcases b12 x hx with h | h
    · exact a11 _ (.inr (toNat_mem_pendSlots _ _ (committedPending_mem _ _ _ h)))
    · exact h.1
  · by_cases hp : x ∈ w.fl.pendingIds
    · exact .inl hp
    · rcases b12 x hx with h | h
      · exact absurd (committedPending_mem _ _ _ h) hp
      · exact .inr ⟨hp, h.2.2⟩

/-- The extent's overflow is its first slot's (the header lies in it, `wb_header`). -/
theorem extent_overflow (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
  have h16 := wb_header w hok f hf
  unfold pageOverflow pageHdr bytesAt
  congr 3
  unfold extentBytes
  rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
    List.flatMap_cons, List.drop_zero, List.drop_zero,
    List.take_append_of_le_length h16]

/-- **`Reload`'s premises** for the synced freelist page, from `wdbOK` (`flCurOK`). -/
theorem reload_premises (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f)
    (hh : w.C.hwm ≤ 2 ^ 62) (hwf : w.fl.WF) :
    let pg := extentBytes w.wb f
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flCountIdx pg).1 < 2 ^ 63 ∧ (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (flIds pg).length + w.fl.pendingIds.length < 2 ^ 63 ∧ (flIds pg ≠ [] ∨ w.fl.free = []) ∧
    f + (1 + pageOverflow (w.wb f)) ≤ w.C.hwm := by
  intro pg
  have hids := flIds_facts w f hok hf
  have hov : pageOverflow pg = pageOverflow (w.wb f) := extent_overflow w f hok hf
  obtain ⟨-, -, -, -, -, a6, -, -, -, -, a11, -⟩ := hok
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, -, -, b10, -, -⟩ := a6 f hf f hf
  have hlen : (flIds pg).length = (flCountIdx pg).1 := by
    simp [flIds]
  have h1 := length_le_of_nodup_two (flIds pg) w.C.hwm (by omega) b6 fun x hx => ⟨(hids x hx).1, (hids x hx).2.1⟩
  have hpnd : w.fl.pendingIds.Nodup := (List.nodup_append.1 hwf.1).2.1
  have h2 := length_le_of_nodup_lt w.fl.pendingIds w.C.hwm hpnd fun x hx =>
    a11 _ (.inr (toNat_mem_pendSlots _ _ hx))
  refine ⟨b4, b5, by omega, b6, b7, by omega, ?_, by rw [← hov]; exact b2⟩
  rcases hfr : w.fl.free with _ | ⟨x, xs⟩
  · exact .inr rfl
  · left; intro he
    have := b10 x (by rw [hfr]; exact List.mem_cons_self ..)
    rw [he] at this; exact absurd this (List.not_mem_nil)

/-- **`store_reload`'s premises** for the synced freelist page's ids. -/
theorem reload_store_ids (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f)
    (hh : w.C.hwm ≤ 2 ^ 62) :
    ∀ x ∈ flIds (extentBytes w.wb f), 2 ≤ x.toNat ∧ x.toNat < w.C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ slotsOf w.C w.fl ∨ x ∈ w.fl.pendingIds) := by
  intro x hx
  obtain ⟨a, b, c⟩ := flIds_facts w f hok hf x hx
  refine ⟨a, b, by omega, ?_⟩
  rcases c with c | ⟨c1, c2⟩
  · exact .inr c
  · left
    rw [mem_slotsOf]
    rintro (h | h)
    · exact c2 ((mem_pagesSlots_iff _ _).1 h)
    · exact c1 ((mem_pendSlots_iff _ _).1 h)

/-- **The writer side after `Reload` of the synced freelist page.** -/
theorem wdbOK_reload_synced (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    wdbOK { w with fl := w.fl.reload (flIds (extentBytes w.wb f)) } := by
  have hids := flIds_facts w f hok hf
  have hfr : ∀ x ∈ (w.fl.reload (flIds (extentBytes w.wb f))).free,
      x ∈ flIds (extentBytes w.wb f) ∧ x.toNat < w.C.hwm ∧ ¬ coversSlot w.C.pages x.toNat := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_reload_free _ _ _ hx
    obtain ⟨-, b, c⟩ := hids x h1
    rcases c with c | ⟨-, c⟩
    · exact absurd c h2
    · exact ⟨h1, b, c⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hok
  refine ⟨c1, c2, c3, c4, ?_, ?_, c7, c8, c9, c10, c11, ?_, c13, c14, c15⟩
  · intro x hx ht
    exact (hfr x hx).2.2 ((mem_pagesSlots_iff _ _).1 ht)
  · intro f' hf'
    simp only at hf' ⊢
    rw [hf] at hf'; cases hf'
    intro g hg
    rw [hf] at hg; cases hg
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := c6 f hf f hf
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun s h1 h2 => ⟨(a9 s h1 h2).1, fun hm => ?_⟩,
      fun x hx => (hfr x hx).1, a11, a12⟩
    rcases List.mem_append.1 hm with hm | hm
    · have hx := (hfr _ hm).1
      have hlt : s < 2 ^ 64 := by
        have := c11; have := (a9 s h1 h2); omega
      apply a8 _ hx
      rw [toNat_W64_of_lt _ (by omega)]
      exact ⟨h1, h2⟩
    · exact (a9 s h1 h2).2 (List.mem_append_right _ hm)
  · intro x hx; exact (hfr x hx).2.1

end pure

end bbolt
end EtcdGrove
end Perennial
