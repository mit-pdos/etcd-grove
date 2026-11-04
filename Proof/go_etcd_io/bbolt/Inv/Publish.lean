/-
The writer side at the commit point (batch 39 of `notes/bbolt-proof-plan.md`, for `Commit`, U10):
`store_publish` moves the new tree's slots `S` from the writer's `W` slots into the store and the
committed state `C → C'`; the writer's record after it is `{w with C := C', W := W \ S}`
(`WDb.publish`), and `wdbOK` holds of it (`wdbOK_publish`) under `store_publish`'s own side conditions
plus the new state's bounds and the new synced freelist page's `flCurOK` (its bytes are the
writer's `wb`: the freelist page is no store slot).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt

section publish
variable [GooseExts]

/-- The writer's record after the publish of `C'` with the new tree slots `S`. -/
def WDb.publish (w : WDb) (C' : CommitSt) (S : List Nat) : WDb :=
  { w with C := C', W := w.W.filter (fun s => decide (s ∉ S)) }

proj_simps WDb.publish

theorem mem_slotsOf (C : CommitSt) (fl : FLPg) (s : Nat) :
    s ∈ slotsOf C fl ↔ s ∈ treeSlots C ∨ s ∈ pendSlots fl := by
  simp only [slotsOf, mem_list_dedup, List.mem_append]

/-- **`wdbOK` after the publish.** `hdrop`, `hS`, `hnp` are `store_publish`'s; `hSf` its `hSb`'s
"not free"; `hflc` the new synced freelist page's (if any) `flCurOK` over the writer's bytes (the
freelist after the commit is the writer's `w.fl`); the rest are the new state's bounds (`htb`:
the new tree's slots below its high-water mark, `treeOK`'s; `hsize`, `hmap`: `Commit` grew the
file and the mapping covers the mark, spill's `pgid · 4096 ≤ mapLen`). -/
theorem wdbOK_publish (w : WDb) (C' : CommitSt) (S : List Nat) (hok : wdbOK w)
    (hdrop : ∀ s ∈ treeSlots w.C, s ∉ treeSlots C' → s ∈ pendSlots w.fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots C' ∧ s ∉ slotsOf w.C w.fl)
    (hnp : ∀ s ∈ treeSlots C', s ∉ pendSlots w.fl)
    (hSf : ∀ s ∈ S, W64 (s : Int) ∉ w.fl.free)
    (hflc : ∀ f, C'.flpg = some f → flCurOK w.fl C' (extentBytes w.wb f))
    (htx : C'.txid + 1 < 2 ^ 64) (hhwm64 : C'.hwm < 2 ^ 64) (hmono : w.C.hwm ≤ C'.hwm)
    (hsize : C'.hwm * 4096 ≤ w.m.size) (hmap : ∀ b l, w.ms = some (b, l) → C'.hwm * 4096 ≤ l)
    (htb : ∀ s ∈ treeSlots C', s < C'.hwm) :
    wdbOK (w.publish C' S) := by
  obtain ⟨h1, h2, _h3, h4, h5, _h6, _h7, _h8, _h9, h10, h11, h12, h13, h14, h15⟩ := hok
  simp only [wdbOK, WDb.publish]
  refine ⟨h1, h2, hsize, ?_, ?_, hflc, htx, hhwm64, hmap, h10, ?_, ?_, h13, h14, ?_⟩
  · intro s
    rw [List.mem_filter, h4 s, decide_eq_true_iff]
    constructor
    · rintro ⟨⟨hs2, hsM, hst, hsp⟩, hsS⟩
      refine ⟨hs2, hsM, fun ht' => hsS ((hS s).2 ⟨ht', ?_⟩), hsp⟩
      rw [mem_slotsOf]; rintro (h | h)
      · exact hst h
      · exact hsp h
    · rintro ⟨hs2, hsM, hst', hsp⟩
      refine ⟨⟨hs2, hsM, fun ht => hst' ?_, hsp⟩, fun hsS => hst' ((hS s).1 hsS).1⟩
      exact Classical.byContradiction fun hn => hsp (hdrop s ht hn)
  · intro x hx ht'
    by_cases hxS : x.toNat ∈ S
    · apply hSf _ hxS
      have : W64 ((x.toNat : Nat) : Int) = x := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [this]; exact hx
    · have hm : x.toNat ∈ slotsOf w.C w.fl :=
        Classical.byContradiction fun hn => hxS ((hS _).2 ⟨ht', hn⟩)
      rw [mem_slotsOf] at hm
      rcases hm with h | h
      · exact h5 x hx h
      · exact hnp _ ht' h
  · intro s hs
    rcases hs with hs | hs
    · exact htb s hs
    · have := h11 s (Or.inr hs); omega
  · intro x hx; have := h12 x hx; omega
  · intro s hs; exact h15 s (List.mem_filter.1 hs).1

end publish

end bbolt
end EtcdGrove
end Perennial
