/-
`node.spill` after its children's loop (U9z2, `notes/bbolt-proof-plan.md`; pure): **the slots'
bookkeeping across a piece's step** (`pcStep`): the pending slots kept and the piece's freed page
made pending (`pcStep_pend`), the new run no pending slot (`pcStep_id_pend`) and new
(`pcStep_newSlot`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section slots
variable [GooseExts] [GoGlobalContext]

/-- **A piece's step keeps the pending slots** and makes the piece's own page's (`ownSl`)
pending. -/
theorem pcStep_pend {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hb : ∀ s ∈ ownSl Xi.v rl.nv.pgid', s < 2 ^ 62) :
    ∀ y, y ∈ pendSlots wi.fl ∨ y ∈ ownSl Xi.v rl.nv.pgid' → y ∈ pendSlots w2.fl := by
  obtain ⟨X1, w1, X2, p, ra, rp, s0, ins, stf, sta, hfr, -, hal, -⟩ := hs
  have h2 := (allocRes_fl hal).1
  intro y hy
  rw [h2]
  rcases hy with hy | hy
  · exact (pcFreed_fl hfr).1 y hy
  · rcases hfr with ⟨hp0, -, -, -⟩ | ⟨pg, hp0, hpg, -, rfl, -⟩
    · unfold ownSl at hy; rw [if_pos hp0] at hy; simp at hy
    · unfold ownSl at hy hb; rw [if_neg hp0] at hy hb
      have he : pgSlots Xi.v.pages [rl.nv.pgid'.toNat] =
          List.range' rl.nv.pgid'.toNat (1 + pageOverflow pg) := by
        unfold pgSlots; simp [hpg]
      rw [he] at hy hb
      have hlast := hb (rl.nv.pgid'.toNat + pageOverflow pg)
        (List.mem_range'_1.2 ⟨by omega, by omega⟩)
      obtain ⟨h1, h3⟩ := List.mem_range'_1.1 hy
      exact (pendSlots_freePages _ _ _ _ (by omega) y).2 (Or.inr ⟨h1, h3⟩)

/-- **A piece's new run starts at no pending slot** (a free id is no pending id; the mark is above
every pending id). -/
theorem pcStep_id_pend {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {L : List Nat} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat L) : id.toNat ∉ pendSlots wi.fl := by
  obtain ⟨X1, w1, X2, p, ra, rp, s0, ins, stf, sta, hfr, -, hal, -⟩ := hs
  obtain ⟨hmv, -, -, -, -, -, -, hfree, -⟩ := pcFreed_basic hfr
  have hc0 : 0 < count := hal.1
  intro hm
  obtain ⟨z, hz, hze⟩ := List.mem_map.1 hm
  have hzi : z = id := BitVec.eq_of_toNat_eq hze
  rw [hzi] at hz
  rcases (allocRes_basic hal).2.2.2.2 with ⟨hcan, -, -⟩ | ⟨hid, -, -, -⟩
  · have hin : id ∈ w1.fl.free := hcan.2 id (by unfold inRun; omega)
    rw [hfree] at hin
    exact (List.nodup_append.1 hsl.2.2.1).2.2 id hin id hz rfl
  · have := hsl.2.2.2 id (List.mem_append_right _ hz)
    rw [hid, hmv] at this; omega

/-- **A piece's new run is new**: allocated by its steps, or at the mark. -/
theorem pcStep_newSlot {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id) :
    ∀ y ∈ List.range' id.toNat count, newSlot st Xi.t.mv.pgid'.toNat y := by
  obtain ⟨X1, w1, X2, p, ra, rp, s0, ins, stf, sta, hfr, rfl, hal, -, hsta, -⟩ := hs
  obtain ⟨hmv, -⟩ := pcFreed_basic hfr
  intro y hy
  obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hy
  rcases hsta with rfl | ⟨-, hid⟩
  · exact Or.inl ⟨id, count, by simp, h1, h2⟩
  · right; rw [← hmv, ← hid]; exact h1

end slots

end Spill

end bbolt
end EtcdGrove
end Perennial
