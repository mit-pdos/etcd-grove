/-
**`cut`'s new segment name** (W2 of `notes/wal-fsext-plan.md`, step 3; pure): `w.seq()` parses the
tail's name `child dir (walFileName sq ix)` (its `filepath.Base` the segment name, which
`parseWALName` reads back as `(sq, ix)`), and the new name `walName(sq + 1, next + 1)` sorts after
every name below or at the old one (`walFileName_lt`: fixed-width hexadecimal, compared byte-wise).
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames
public import LinuxFs.Proof.path.filepath.Names
public import Proof.fmt.WalName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

section pure
variable [GooseExts]

/-- A lexicographic order survives appending to two lists of the same length. -/
theorem lex_append_eqlen {α : Type} {r : α → α → Prop} :
    ∀ {l1 l2 : List α} (s t : List α), List.Lex r l1 l2 → l1.length = l2.length →
      List.Lex r (l1 ++ s) (l2 ++ t)
  | [], [], _, _, h, _ => nomatch h
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: l1, b :: l2, s, t, h, hl => by
    cases h with
    | cons h' => exact List.Lex.cons (lex_append_eqlen s t h' (by simpa using hl))
    | rel hr => exact List.Lex.rel hr

/-- Two lists differing first at a position past a common prefix. -/
theorem lex_prefix {α : Type} {r : α → α → Prop} (p : List α) {x y : α} (s t : List α)
    (h : r x y) : List.Lex r (p ++ x :: s) (p ++ y :: t) := by
  induction p with
  | nil => exact List.Lex.rel h
  | cons a p ih => exact List.Lex.cons ih

/-- Hexadecimal digits sort as their values. -/
theorem hexDigitByte_lt : ∀ (d1 d2 : Fin 16), d1 < d2 →
    uint.Z (_root_.Perennial.fmt.hexDigitByte d1.val) < uint.Z (_root_.Perennial.fmt.hexDigitByte d2.val) := by
  decide

/-- **Fixed-width hexadecimal sorts as the numbers.** -/
theorem hexPad_lt : ∀ (w a b : Nat), a < b → b < 16 ^ w →
    go.GoStringLt (fmt.hexPad w a) (fmt.hexPad w b)
  | 0, a, b, hab, hb => by simp at hb; omega
  | w + 1, a, b, hab, hb => by
    simp only [fmt.hexPad]
    have hb' : b / 16 < 16 ^ w := by rw [Nat.pow_succ] at hb; omega
    by_cases hq : a / 16 < b / 16
    · exact lex_append_eqlen _ _ (hexPad_lt w _ _ hq hb') (by simp [fmt.length_hexPad])
    · have hq' : a / 16 = b / 16 := by
        have : a / 16 ≤ b / 16 := Nat.div_le_div_right (Nat.le_of_lt hab)
        omega
      rw [hq']
      have hr : a % 16 < b % 16 := by omega
      exact lex_prefix _ [] [] (hexDigitByte_lt ⟨a % 16, Nat.mod_lt _ (by decide)⟩
        ⟨b % 16, Nat.mod_lt _ (by decide)⟩ hr)

/-- **A segment name with a larger sequence number sorts after.** -/
theorem walFileName_lt (sq ix sq' ix' : Nat) (h : sq < sq') (h' : sq' < 2 ^ 64) :
    go.GoStringLt (walFileName sq ix) (walFileName sq' ix') := by
  unfold walFileName
  simp only [hex16_hexPad, List.append_assoc]
  have h16 : sq' < 16 ^ 16 := lt_of_lt_of_eq h' (by decide)
  have hl : go.GoStringLt (fmt.hexPad 16 sq) (fmt.hexPad 16 sq') := hexPad_lt 16 sq sq' h h16
  unfold go.GoStringLt at hl ⊢
  exact lex_append_eqlen _ _ hl (by rw [fmt.length_hexPad, fmt.length_hexPad])

/-- No hexadecimal digit is `/`. -/
theorem hexDigit_ne_slash : ∀ k : Fin 16, hexDigit k.val ≠ (47 : w8) := by decide

theorem hex16_ne_slash (n : Nat) : ∀ c ∈ hex16 n, c ≠ (47 : w8) := by
  intro c hc
  unfold hex16 at hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact hexDigit_ne_slash ⟨_, Nat.mod_lt _ (by decide)⟩

/-- A segment name is a clean path segment (no `/`, not `.` or `..`). -/
theorem cleanSeg_walFileName (sq ix : Nat) : path.cleanSeg (walFileName sq ix) := by
  have hl := walFileName_length sq ix
  refine ⟨fun e => by rw [e] at hl; simp at hl, ?_, fun e => by rw [e] at hl; simp at hl,
    fun e => by rw [e] at hl; simp at hl⟩
  intro c hc
  unfold walFileName at hc
  simp only [List.mem_append] at hc
  rcases hc with ((h | h) | h) | h
  · exact hex16_ne_slash sq c h
  · simp at h; subst h; decide
  · exact hex16_ne_slash ix c h
  · simp at h; rcases h with h | h | h | h <;> (subst h; decide)

/-- **`filepath.Base` of a segment's path** in the directory `dir`: the segment name. -/
theorem baseModel_child_walFileName (dir : GoString) (sq ix : Nat) :
    path.baseModel (child dir (walFileName sq ix)) = walFileName sq ix := by
  have := filepath.baseModel_name dir (walFileName sq ix) (cleanSeg_walFileName sq ix)
  simpa [child, slashB, List.append_assoc] using this

/-- **`parseWALName` of a segment name** reads its numbers back. -/
theorem scanWalName_walFileName (sq ix : Nat) :
    go!".wal" <:+ walFileName sq ix ∧
      fmt.scanWalName (walFileName sq ix) = .ok (W64 sq) (W64 ix) := by
  rw [walFileName_walNameStr]
  refine ⟨⟨fmt.hexPad 16 (uint.nat (BitVec.ofNat 64 sq)) ++ W8 45 ::
      fmt.hexPad 16 (uint.nat (BitVec.ofNat 64 ix)), by simp [fmt.walNameStr]⟩, ?_⟩
  exact fmt.scanWalName_walNameStr _ _

end pure

end WalFs
end EtcdGrove
end Perennial

end
