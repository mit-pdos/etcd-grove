/-
**When Go's `strings.ToLower` returns a given lower-case ASCII word** (etcdstorage, 2026-11-20; the
vocabulary of `Spec/strings/ToLower.lean`'s post, `notes/axiom-review/getenv-etcd-verify.md`).
Lean-first.

`strings.ToLower(s)` maps `s` rune by rune with `unicode.ToLower` (`strings.Map`; its ASCII fast path
agrees), decoding each invalid UTF-8 byte as `utf8.RuneError`, whose encoding is not ASCII. So its
result is an ASCII word `w` (bytes below `0x80`, no upper-case letter) exactly when `s` is the
concatenation of one encoding, per byte `b` of `w`, of a rune that `unicode.ToLower` maps to `b`.
Those runes, measured with go1.27.3 by enumerating every rune (`notes/axiom-review/getenv-etcd-verify.md`):
`b` itself; for a lower-case letter, its upper-case letter; U+0130 (`İ`, `C4 B0`) for `i` and
U+212A (KELVIN SIGN, `E2 84 AA`) for `k`; no other rune maps to an ASCII byte.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- The encodings of the runes Go's `unicode.ToLower` maps to the ASCII byte `b` (not an upper-case
letter; see the file header). -/
def strings.lowerAlts (b : w8) : List GoString :=
  [b] :: ((if W8 97 ≤ b ∧ b ≤ W8 122 then [[b - W8 32]] else []) ++
    (if b = W8 105 then [[W8 0xC4, W8 0xB0]] else []) ++
    (if b = W8 107 then [[W8 0xE2, W8 0x84, W8 0xAA]] else []))

/-- **`strings.ToLower(s)` is the ASCII word `w`** (for `w` a `lowerWord`; see the file header): `s`
is, byte of `w` by byte, the encoding of a rune that lower-cases to it (`lowerAlts`). -/
def strings.lowersTo : GoString → GoString → Bool
  | s, [] => s.isEmpty
  | s, b :: w => (strings.lowerAlts b).any fun p =>
      p.isPrefixOf s && strings.lowersTo (s.drop p.length) w

/-- An ASCII word with no upper-case letter (a possible result of `strings.ToLower` that
`lowersTo` describes). As `metadata.lowerKey`. -/
def strings.lowerWord (w : GoString) : Prop := ∀ b ∈ w, b < W8 128 ∧ ¬ (W8 65 ≤ b ∧ b ≤ W8 90)

instance (w : GoString) : Decidable (strings.lowerWord w) := by
  unfold strings.lowerWord; infer_instance

end EtcdGrove
end Perennial
