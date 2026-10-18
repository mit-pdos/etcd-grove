/-
Valid UTF-8 as Go's `unicode/utf8` defines it (`utf8.ValidString`; D19l (iii), 2026-10-18): the
byte sequences the Unicode standard calls well-formed (Table 3-7), which are the ones Go's
`ValidString` accepts (its `first`/`acceptRanges` tables, `utf8.go`): no overlong form, no
surrogate (`U+D800..U+DFFF`), nothing above `U+10FFFF`. Decidable: `decide` checks a literal.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- The leading byte `n` of a multi-byte sequence (`≥ 0x80`): its number of continuation bytes
and the range of the first one (`acceptRanges`), or `none` if no sequence starts with it. -/
def utf8Lead (n : Nat) : Option (Nat × Nat × Nat) :=
  if 0xC2 ≤ n ∧ n ≤ 0xDF then some (1, 0x80, 0xBF)
  else if n = 0xE0 then some (2, 0xA0, 0xBF)
  else if 0xE1 ≤ n ∧ n ≤ 0xEC then some (2, 0x80, 0xBF)
  else if n = 0xED then some (2, 0x80, 0x9F)
  else if 0xEE ≤ n ∧ n ≤ 0xEF then some (2, 0x80, 0xBF)
  else if n = 0xF0 then some (3, 0x90, 0xBF)
  else if 0xF1 ≤ n ∧ n ≤ 0xF3 then some (3, 0x80, 0xBF)
  else if n = 0xF4 then some (3, 0x80, 0x8F)
  else none

/-- Whether a byte string is valid UTF-8 (Go's `utf8.ValidString`). -/
def utf8ValidB : List w8 → Bool
  | [] => true
  | b :: bs =>
    if b.toNat < 0x80 then utf8ValidB bs else
    match utf8Lead b.toNat, bs with
    | some (1, lo, hi), c1 :: r =>
        (lo ≤ c1.toNat && c1.toNat ≤ hi) && utf8ValidB r
    | some (2, lo, hi), c1 :: c2 :: r =>
        (lo ≤ c1.toNat && c1.toNat ≤ hi) && (0x80 ≤ c2.toNat && c2.toNat ≤ 0xBF) && utf8ValidB r
    | some (3, lo, hi), c1 :: c2 :: c3 :: r =>
        (lo ≤ c1.toNat && c1.toNat ≤ hi) && (0x80 ≤ c2.toNat && c2.toNat ≤ 0xBF) &&
          (0x80 ≤ c3.toNat && c3.toNat ≤ 0xBF) && utf8ValidB r
    | _, _ => false

/-- `s` is valid UTF-8 (what Go's `utf8.ValidString(s)` returns). -/
def utf8Valid (s : GoString) : Prop := utf8ValidB s = true

instance (s : GoString) : Decidable (utf8Valid s) := by unfold utf8Valid; infer_instance

/-- ASCII: every byte below `0x80`. -/
def asciiStr (s : GoString) : Prop := ∀ b ∈ s, b.toNat < 0x80

instance (s : GoString) : Decidable (asciiStr s) := by unfold asciiStr; infer_instance

theorem utf8Valid_of_ascii : ∀ (s : GoString), asciiStr s → utf8Valid s
  | [], _ => rfl
  | b :: bs, h => by
    have hb : b.toNat < 0x80 := h b (List.mem_cons_self ..)
    have ih := utf8Valid_of_ascii bs (fun c hc => h c (List.mem_cons_of_mem _ hc))
    unfold utf8Valid at ih ⊢
    unfold utf8ValidB; rw [if_pos hb]
    exact ih

theorem asciiStr_append {s t : GoString} (hs : asciiStr s) (ht : asciiStr t) :
    asciiStr (s ++ t) := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact hs b h
  · exact ht b h

example : utf8Valid go!"Range" := by decide
example : utf8Valid go!"é" := by decide
example : ¬ utf8Valid [BitVec.ofNat 8 0xC0, BitVec.ofNat 8 0x80] := by decide

end EtcdGrove
end Perennial
