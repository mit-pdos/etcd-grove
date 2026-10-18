/-
The shape of `semver.Version.String()`'s result (D19l (iii), 2026-10-18): it starts with the
major and minor versions in decimal, each followed by a dot (`version.go`: `"%d.%d.%d"`, then
`-pre` and `+metadata`), which is what `version.Cluster` keeps of it.
-/
module

public import Proof.unicode.utf8.Valid

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- A non-empty string of ASCII decimal digits (`%d` of an unsigned integer). -/
def decDigits (a : GoString) : Prop := a ≠ [] ∧ ∀ c ∈ a, 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- `s` starts with two decimal numbers, each followed by a dot (a `semver.Version`'s
`String()`). -/
def semverStr (s : GoString) : Prop :=
  ∃ a b r : GoString, s = a ++ go!"." ++ b ++ go!"." ++ r ∧ decDigits a ∧ decDigits b

theorem asciiStr_of_decDigits {a : GoString} (h : decDigits a) : asciiStr a := by
  intro c hc
  have := (h.2 c hc).2
  omega

end EtcdGrove
end Perennial
