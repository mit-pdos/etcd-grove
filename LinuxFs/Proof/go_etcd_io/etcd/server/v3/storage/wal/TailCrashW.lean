/- Lean-first (no Rocq counterpart).

# The crash of a tail in a resize window (W6, I3b; pure; W6 log, twenty-third session)

`crashTo_tailL` (`TailCrash.lean`) decodes a crash of an exact tail: the image no longer than its bytes,
each byte one of their candidates (`TailCands`). A write past the preallocated size, and every write
in a resize window after it or after `cut`'s truncate, leaves the tail in a window: a crash may leave it
up to `om.hi` long, its bytes past the size those its `OsMeta` knows (`segBytesX`), and the candidates
from the write position on of the window's shapes (`WinShape`: `old`'s byte stamped 0, a known
resize's zero, the stream's byte stamped by a write). Here the decoding over such candidates:

* `TailShape`: what the decoding needs of the candidates (in place of `TailCands`' exact form): below
  `so` the durable intended byte; from `so` on, each candidate the intended byte or (past `max so z0`)
  a zero, those stamped 0 the byte under the stream, one stamped 0 below `z0`, those of a write (a
  positive stamp no resize's) the intended byte. `TailCands.shape` (exact tails), `tailShape_win`
  (from `ByteOk` below `wr` and `WinShape` from `wr` on).
* `TailShape.vals`/`TailShape.asOf`: the image's values and W1 (`AsOfW`, the resize amendment's: a
  frame as of a change is as of a write) as `tail_decodeV` reads them.
* `crashTo_tailW`: `crashTo_tailL` for a tail in a window (the image up to `segBytesX`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section shape

/-- **The candidates `cs` of a crashed tail's bytes, as the decoding reads them** (see the file header):
the intended stream `X`, the synced offset `so`, the end `z0` of the frames found at the generation's
start, the known resizes' stamps `rz`. -/
structure TailShape (X : Nat → w8) (so z0 : Nat) (rz : List Nat) (cs : Nat → Cands) : Prop where
  synced : ∀ b, b < so → cs b = [(X b, 0)]
  val : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → q.1 = X b ∨ (max so z0 ≤ b ∧ q.1 = 0)
  zero : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → q.2 = 0 → q.1 = if b < z0 then X b else 0
  head : ∀ b, so ≤ b → b < z0 → ∃ q ∈ cs b, q.2 = 0
  pos : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → 0 < q.2 → q.2 ∉ rz → q.1 = X b

variable {X : Nat → w8} {so z0 : Nat} {rz : List Nat} {cs : Nat → Cands}

/-- The image's values (`tail_decodeV`'s `TailVals`). -/
theorem TailShape.vals (h : TailShape X so z0 rz cs) {img : List w8}
    (himg : ∀ b, b < img.length → ∃ s, (img.getD b 0, s) ∈ cs b) : TailVals X so z0 img := by
  intro b hb
  obtain ⟨s, hs⟩ := himg b hb
  by_cases hbs : b < so
  · rw [h.synced b hbs, List.mem_singleton] at hs
    exact .inl (Prod.mk.inj hs).1
  · exact h.val b _ (by omega) hs

/-- W1 of a frame core (`AsOfW`) as the decoding reads it (`TailAsOf`). -/
theorem TailShape.asOf (h : TailShape X so z0 rz cs) {img : List w8} {o len : Nat}
    (ha : AsOfW cs rz (fun b => img.getD b 0) o len) : TailAsOf X so z0 img o len := by
  rcases ha with ha | ⟨n, hn, ha⟩
  · left
    intro b h1 h2
    have hb := ha b h1 h2
    dsimp only at hb
    rw [hb]
    by_cases hbs : b < so
    · rw [h.synced b hbs, valAt_single, if_pos (by omega)]
    · rw [valAt_latestAt]
      cases hl : latestAt (cs b) 0 with
      | some p =>
        obtain ⟨hpm, hp0⟩ := latestAt_mem hl
        simp only [Option.map_some, Option.getD_some]
        rw [h.zero b p (by omega) hpm (by omega)]
        by_cases hz : b < z0
        · rw [if_pos hz, if_pos (by omega)]
        · rw [if_neg hz, if_neg (by omega)]
      | none =>
        simp only [Option.map_none, Option.getD_none]
        by_cases hz : b < z0
        · exfalso
          obtain ⟨q, hq, hq0⟩ := h.head b (by omega) hz
          unfold latestAt at hl
          rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hl
          exact hl q hq (by simp [hq0])
        · rw [if_neg (by omega)]
  · right
    intro b h1 h2
    obtain ⟨p, hp, hv, hp0, hpr⟩ := ha b h1 h2
    obtain ⟨hpm, -⟩ := latestAt_mem hp
    dsimp only at hv
    rw [hv]
    by_cases hbs : b < so
    · rw [h.synced b hbs, List.mem_singleton] at hpm; subst hpm; simp at hp0
    · exact h.pos b p (by omega) hpm hp0 hpr

/-- An exact tail's candidates (`TailCands`) have the shape, for any resizes known. -/
theorem TailCands.shape {Y : Nat → w8} (h : TailCands X Y cs so z0) (rz : List Nat) :
    TailShape X so z0 rz cs where
  synced := h.synced
  val := fun b q _ hq => h.mem_val (v := q.1) (s := q.2) hq
  zero := by
    intro b q hb hq hq0
    obtain ⟨ex, he, hex⟩ := h.unsynced b hb
    rw [he] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · by_cases hz : b < z0
      · rw [if_pos hz]; exact h.old_lo b hz
      · rw [if_neg hz]; exact h.old_hi b (by omega)
    · have := (hex q hq).2; omega
  head := fun b hb _ => by
    obtain ⟨ex, he, -⟩ := h.unsynced b hb
    exact ⟨_, by rw [he]; exact List.mem_cons_self .., rfl⟩
  pos := fun b q hb hq hq0 _ => by
    obtain ⟨ex, he, hex⟩ := h.unsynced b hb
    rw [he] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simp at hq0
    · exact (hex q hq).1

/-- **A window's candidates have the shape** (`TailWin`'s): below `wr` each byte's `ByteOk`, from `wr`
on each candidate `WinShape`; the stream `S` is `old` below `z0` and `old` zero from `z0` on (F-Z). -/
theorem tailShape_win {S old : List w8} {wr : Nat} (hso : so ≤ wr) (hz0 : z0 ≤ wr)
    (hlow : ∀ b, b < wr → ∃ (y : ByteG) (a w : Bool), cs b = y.2 ∧
      ByteOk (S.getD b 0) (old.getD b 0) a w (decide (b < so)) y)
    (hhi : ∀ b q, wr ≤ b → q ∈ cs b → WinShape S old rz b q)
    (htake : S.take z0 = old.take z0) (hZ : ∀ b, z0 ≤ b → b < old.length → old.getD b 0 = 0) :
    TailShape (fun b => S.getD b 0) so z0 rz cs := by
  have hlo : ∀ b, b < z0 → old.getD b 0 = S.getD b 0 := by
    intro b hb
    have h1 := congrArg (fun l => l.getD b 0) htake
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hb] at h1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; exact h1.symm
  have hhi0 : ∀ b, z0 ≤ b → old.getD b 0 = 0 := by
    intro b hb
    by_cases hbo : b < old.length
    · exact hZ b hb hbo
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have hold : ∀ b, old.getD b 0 = if b < z0 then S.getD b 0 else 0 := by
    intro b; split
    · exact hlo b (by omega)
    · exact hhi0 b (by omega)
  -- below `wr`, not synced: `(old b, 0)` first, then the stream's byte stamped positive
  have hun : ∀ b, so ≤ b → b < wr → ∃ ex : Cands, cs b = (old.getD b 0, 0) :: ex ∧
      ∀ q ∈ ex, q.1 = S.getD b 0 ∧ 0 < q.2 := by
    intro b h1 h2
    obtain ⟨y, a, w, hc, hy⟩ := hlow b h2
    rw [show decide (b < so) = false by simp; omega] at hy
    simp only [ByteOk, Bool.false_eq_true, ite_false] at hy
    obtain ⟨ex, he, hex, -⟩ := hy
    exact ⟨ex, by rw [hc, he], hex⟩
  refine ⟨fun b hb => ?_, fun b q hb hq => ?_, fun b q hb hq hq0 => ?_, fun b hb hbz => ?_,
    fun b q hb hq hq0 hqr => ?_⟩
  · obtain ⟨y, a, w, hc, hy⟩ := hlow b (by omega)
    rw [show decide (b < so) = true by simp; omega] at hy
    simp only [ByteOk, ite_true] at hy
    rw [hc, hy]
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · dsimp only; rw [hold b]
        split
        · exact .inl rfl
        · exact .inr ⟨by omega, rfl⟩
      · exact .inl (hex q hq).1
    · rcases hhi b q (by omega) hq with rfl | ⟨h1, -⟩ | ⟨-, h1, -⟩
      · dsimp only; exact .inr ⟨by omega, hhi0 b (by omega)⟩
      · exact .inr ⟨by omega, h1⟩
      · exact .inl h1
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hold b
      · have := (hex q hq).2; omega
    · rw [if_neg (by omega)]
      rcases hhi b q (by omega) hq with rfl | ⟨h1, -⟩ | ⟨-, -, h1⟩
      · exact hhi0 b (by omega)
      · exact h1
      · omega
  · obtain ⟨ex, he, -⟩ := hun b hb (by omega)
    exact ⟨_, by rw [he]; exact List.mem_cons_self .., rfl⟩
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · simp at hq0
      · exact (hex q hq).1
    · rcases hhi b q (by omega) hq with rfl | ⟨-, h1⟩ | ⟨-, h1, -⟩
      · simp at hq0
      · exact absurd h1 hqr
      · exact h1

end shape

end WalFs
end EtcdGrove
end Perennial

end
