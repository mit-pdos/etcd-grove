/-
The shape of `semver.Version.String()`'s result (D19l (iii), 2026-10-18): it starts with the
major and minor versions in decimal, each followed by a dot (`version.go`: `"%d.%d.%d"`, then
`-pre` and `+metadata`), which is what `version.Cluster` keeps of it. Since 2026-11-23
(prove-ps2-semstr, `String` proved over the real code) the exact string, `semver.render`, of which
`semverStr` is a consequence (`semver.semverStr_render`).
-/
module

public import Proof.unicode.utf8.Valid
public import GeneratedProof.github_com.Masterminds.semver.v3
public import Perennial.Proof.fmt.Base

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- A non-empty string of ASCII decimal digits (`%d` of an unsigned integer). -/
def decDigits (a : GoString) : Prop := a ≠ [] ∧ ∀ c ∈ a, 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- `s` starts with two decimal numbers, each followed by a dot (a `semver.Version`'s
`String()`). -/
def semverStr (s : GoString) : Prop :=
  ∃ a b r : GoString, s = a ++ go!"." ++ b ++ go!"." ++ r ∧ decDigits a ∧ decDigits b

/-- **`v.String()`** (`version.go:340-352`): `major.minor.patch` in decimal (`fmt`'s `%d` of a
`uint64`), then `-pre` if `pre` is not empty and `+metadata` if `metadata` is not empty. -/
def semver.render [GooseExts] (x : github_com.Masterminds.semver.v3.Version) : GoString :=
  _root_.Perennial.fmt.decimal (uint.Z x.major') ++ go!"." ++
  _root_.Perennial.fmt.decimal (uint.Z x.minor') ++ go!"." ++
  _root_.Perennial.fmt.decimal (uint.Z x.patch') ++
  (if x.pre' = [] then [] else go!"-" ++ x.pre') ++
  (if x.metadata' = [] then [] else go!"+" ++ x.metadata')

theorem decDigits_decimal (n : w64) : decDigits (_root_.Perennial.fmt.decimal (uint.Z n)) := by
  rw [_root_.Perennial.fmt.decimal_of_nonneg (by word)]
  refine ⟨_root_.Perennial.fmt.decimalNat_ne_nil _, fun c hc => ?_⟩
  have := _root_.Perennial.fmt.decimalNat_digits _ c hc
  constructor <;> word

theorem semver.semverStr_render [GooseExts] (x : github_com.Masterminds.semver.v3.Version) :
    semverStr (semver.render x) :=
  ⟨_root_.Perennial.fmt.decimal (uint.Z x.major'), _root_.Perennial.fmt.decimal (uint.Z x.minor'),
    _root_.Perennial.fmt.decimal (uint.Z x.patch') ++
      (if x.pre' = [] then [] else go!"-" ++ x.pre') ++
      (if x.metadata' = [] then [] else go!"+" ++ x.metadata'),
    by simp only [semver.render, List.append_assoc], decDigits_decimal _, decDigits_decimal _⟩

end EtcdGrove
end Perennial
