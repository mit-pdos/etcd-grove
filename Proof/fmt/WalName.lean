/-
**The WAL's segment names, as `fmt` writes and reads them** (pure; WAL leaf specs, 2026-11-13):
`walName(seq, index)` is `fmt.Sprintf("%016x-%016x.wal", seq, index)` and `parseWALName` scans it
back with `fmt.Sscanf(str, "%016x-%016x.wal", &seq, &index)` (util.go:108-118). The specs:
`Spec/fmt/SprintfWalName.lean`, `Spec/fmt/SscanfWalName.lean`.

* `fmt.walNameStr s i`: Go's `%016x` of a `uint64` is its lowercase hexadecimal zero-padded to
  16 digits (exactly 16: the value is below `16^16`).
* `fmt.scanWalName str`: what Go 1.27's scanner (`fmt/scan.go`, `doScanf`) does with that format
  on `str` (`Sscanf` scans with newlines not spaces): for each `%016x` it skips spaces
  (`SkipSpace`: Unicode spaces; a newline is an error), then reads at most 16 runes of hex digits
  of either case (`hexadecimalDigits`, `"0123456789aAbBcCdDeEfF"`; at least one, `scanNumber`),
  parsed by `ParseUint(tok, 16, 64)` (16 digits always fit); `-` and `.wal` must match the input
  rune for rune; whatever follows `.wal` is ignored. The model gives `.ok seq index` or `.err`
  exactly, except where Go skips spaces (at the start, after the `-`): when the byte there may
  begin a space (`fmt.mayBeSpace`: `\t`..`\r`, `' '`, or any byte from `0x80`, which may begin
  a multi-byte space such as U+00A0), it gives `.unknown` and the spec says nothing.

**What `Sscanf` accepts that `walName` never writes** (`.ok`): fewer than 16 digits
(`"1-2.wal"` is `(1, 2)`), upper-case digits (`"A-B.wal"`), anything after `.wal`
(`"0-0.wal.tmp"`, `"0-0.walx"`; `parseWALName` first checks the `.wal` suffix, so these need
it too: `"0-0.wal.wal"`); and (`.unknown`, not modelled) leading spaces before either number
(`" 0-0.wal"`, `"0- 0.wal"`, Go: `(0, 0)`). `fmt.scanWalName_walNameStr` is the round trip.
Lean-first.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- A hexadecimal digit of either case (Go's `hexadecimalDigits`). -/
def fmt.isHexByte (b : w8) : Bool :=
  decide ((48 ≤ uint.Z b ∧ uint.Z b ≤ 57) ∨ (65 ≤ uint.Z b ∧ uint.Z b ≤ 70) ∨
    (97 ≤ uint.Z b ∧ uint.Z b ≤ 102))

/-- A hexadecimal digit's value. -/
def fmt.hexDigitVal (b : w8) : Nat :=
  if uint.nat b ≤ 57 then uint.nat b - 48 else if uint.nat b ≤ 70 then uint.nat b - 55
  else uint.nat b - 87

/-- The value of a run of hexadecimal digits, most significant first. -/
def fmt.hexValue (ds : GoString) : Nat := ds.foldl (fun acc b => acc * 16 + fmt.hexDigitVal b) 0

/-- A byte at which Go's `SkipSpace` may skip (or fail at a newline): `\t` to `\r`, `' '`, or a
byte from `0x80` (which may begin a multi-byte Unicode space). -/
def fmt.mayBeSpace (b : w8) : Bool :=
  decide ((9 ≤ uint.Z b ∧ uint.Z b ≤ 13) ∨ uint.Z b = 32 ∨ 128 ≤ uint.Z b)

/-- The outcome of a scan: the values, an error, or not modelled. -/
inductive fmt.ScanRes where
  | ok (a b : w64)
  | err
  | unknown
  deriving DecidableEq

/-- One `%016x` at the start of `s` (no space there): the value of the run of hex digits and the
rest, or `none` (Go's error) if the run is empty or longer than 16 (the 17th digit then fails to
match the next format byte, `-` or `.`, neither a hex digit). -/
def fmt.scanHex16 (s : GoString) : Option (Nat × GoString) :=
  let ds := s.takeWhile fmt.isHexByte
  if ds = [] ∨ 16 < ds.length then none else some (fmt.hexValue ds, s.drop ds.length)

/-- See the file header. -/
def fmt.scanWalName (s : GoString) : fmt.ScanRes :=
  if s.head?.map fmt.mayBeSpace = some true then .unknown else
  match fmt.scanHex16 s with
  | none => .err
  | some (a, s1) =>
    match s1 with
    | [] => .err
    | b :: s2 =>
      if b ≠ W8 45 then .err else
      if s2.head?.map fmt.mayBeSpace = some true then .unknown else
      match fmt.scanHex16 s2 with
      | none => .err
      | some (c, s3) => if go!".wal" <+: s3 then .ok (W64 a) (W64 c) else .err

/-- `n`'s last `w` hexadecimal digits, lowercase (`fmt.hexDigitByte`), most significant first. -/
def fmt.hexPad : Nat → Nat → GoString
  | 0, _ => []
  | w + 1, n => fmt.hexPad w (n / 16) ++ [_root_.Perennial.fmt.hexDigitByte (n % 16)]

/-- See the file header. -/
def fmt.walNameStr (s i : w64) : GoString :=
  fmt.hexPad 16 (uint.nat s) ++ W8 45 :: (fmt.hexPad 16 (uint.nat i) ++ go!".wal")

/-! Tests. -/
example : fmt.scanWalName go!"1-2.wal" = .ok (W64 1) (W64 2) := by decide
example : fmt.scanWalName go!"A-b.wal.tmp" = .ok (W64 10) (W64 11) := by decide
example : fmt.scanWalName go!"0-0.tmp" = .err := by decide
example : fmt.scanWalName go!"00000000000000000-0.wal" = .err := by decide
example : fmt.scanWalName go!" 0-0.wal" = .unknown := by decide

theorem fmt.length_hexPad (w n : Nat) : (fmt.hexPad w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [fmt.hexPad, ih]

theorem fmt.hexDigitByte_hex {d : Nat} (h : d < 16) :
    fmt.isHexByte (_root_.Perennial.fmt.hexDigitByte d) = true ∧
    fmt.hexDigitVal (_root_.Perennial.fmt.hexDigitByte d) = d := by
  have : d ∈ List.range 16 := List.mem_range.mpr h
  simp only [List.range, List.range.loop, List.mem_cons] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | h <;> first | decide | simp at h

theorem fmt.hexPad_hex (w n : Nat) : ∀ b ∈ fmt.hexPad w n, fmt.isHexByte b = true := by
  induction w generalizing n with
  | zero => simp [fmt.hexPad]
  | succ w ih =>
    intro b hb
    simp only [fmt.hexPad, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih _ b hb
    · exact (fmt.hexDigitByte_hex (Nat.mod_lt n (by omega))).1

theorem fmt.hexValue_hexPad (w n : Nat) : fmt.hexValue (fmt.hexPad w n) = n % 16 ^ w := by
  induction w generalizing n with
  | zero => simp [fmt.hexPad, fmt.hexValue, Nat.mod_one]
  | succ w ih =>
    have h1 := ih (n / 16)
    simp only [fmt.hexValue] at h1
    simp only [fmt.hexPad, fmt.hexValue, List.foldl_append, List.foldl_cons, List.foldl_nil, h1,
      (fmt.hexDigitByte_hex (Nat.mod_lt n (by omega : 0 < 16))).2]
    rw [Nat.pow_succ, Nat.mul_comm (16 ^ w) 16, Nat.mod_mul]
    omega

theorem fmt.takeWhile_hexPad (w n : Nat) (b : w8) (rest : GoString) (hb : fmt.isHexByte b = false) :
    (fmt.hexPad w n ++ b :: rest).takeWhile fmt.isHexByte = fmt.hexPad w n := by
  rw [List.takeWhile_append_of_pos (fmt.hexPad_hex w n)]
  simp [hb]

theorem fmt.scanHex16_hexPad (n : Nat) (b : w8) (rest : GoString) (hb : fmt.isHexByte b = false) :
    fmt.scanHex16 (fmt.hexPad 16 n ++ b :: rest) = some (n % 16 ^ 16, b :: rest) := by
  unfold fmt.scanHex16
  simp only [fmt.takeWhile_hexPad 16 n b rest hb, fmt.length_hexPad, fmt.hexValue_hexPad]
  have hne : fmt.hexPad 16 n ≠ [] := by
    intro h; have := fmt.length_hexPad 16 n; rw [h] at this; simp at this
  simp [hne, List.drop_left' (fmt.length_hexPad 16 n)]

theorem fmt.hexPad_cons (n : Nat) :
    ∃ b l, fmt.hexPad 16 n = b :: l ∧ fmt.mayBeSpace b = false := by
  obtain ⟨b, l, hbl⟩ : ∃ b l, fmt.hexPad 16 n = b :: l := by
    cases h : fmt.hexPad 16 n with
    | nil => have := fmt.length_hexPad 16 n; rw [h] at this; simp at this
    | cons b l => exact ⟨b, l, rfl⟩
  refine ⟨b, l, hbl, ?_⟩
  have hb := fmt.hexPad_hex 16 n b (by rw [hbl]; simp)
  revert hb
  simp only [fmt.isHexByte, fmt.mayBeSpace, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-- **The round trip**: `parseWALName`'s scan of `walName(s, i)` gives `(s, i)`. -/
theorem fmt.scanWalName_walNameStr (s i : w64) : fmt.scanWalName (fmt.walNameStr s i) = .ok s i := by
  have hdash : fmt.isHexByte (W8 45) = false := by decide
  have hdot : fmt.isHexByte (W8 46) = false := by decide
  have hlt : ∀ x : w64, uint.nat x % 16 ^ 16 = uint.nat x := fun x =>
    Nat.mod_eq_of_lt (by have : uint.nat x < 2 ^ 64 := (by word); rw [show (16 : Nat) ^ 16 = 2 ^ 64 from rfl]; exact this)
  obtain ⟨b1, l1, h1, hb1⟩ := fmt.hexPad_cons (uint.nat s)
  obtain ⟨b2, l2, h2, hb2⟩ := fmt.hexPad_cons (uint.nat i)
  unfold fmt.scanWalName fmt.walNameStr
  rw [fmt.scanHex16_hexPad _ _ _ hdash, hlt, h1]
  simp only [List.cons_append, List.head?_cons, Option.map_some, hb1, ne_eq, not_true_eq_false,
    ite_false, Option.some.injEq, Bool.false_eq_true]
  have hgo : go!".wal" = W8 46 :: go!"wal" := rfl
  rw [hgo, fmt.scanHex16_hexPad _ _ _ hdot, hlt, h2]
  simp [hb2]

end EtcdGrove
end Perennial
