/-
**Versions of a simple form parse** (the trust boundary, `semver`; rafthttp stage 5e-2, accepted by
the user 2026-10-23). Lean-first.

`semverSimple s`: `MAJOR.MINOR.PATCH`, each a decimal of at most 9 digits without a leading zero,
optionally followed by `-` and a prerelease of non-empty dot-separated identifiers of ASCII
letters, digits and `-`, a numeric identifier without a leading zero. A subset of what
Masterminds' `NewVersion` accepts (its regular expression, `v?([0-9]+)(\.[0-9]+)?(\.[0-9]+)?` then
an optional `-` prerelease and `+` metadata, with the numbers parsed as `uint64` and a numeric
prerelease identifier refused with a leading zero): `semverValid_simple` says so. What the stream
reader parses: `version.Version` (`"3.8.0-alpha.0"`) and `serverVersion`'s default (`"2.0.0"`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace semver

/-- `l` split at each `sep`. -/
def splitBy (sep : w8) : List w8 → List (List w8)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitBy sep cs
    else match splitBy sep cs with
      | [] => [[c]]
      | g :: gs => (c :: g) :: gs

def isDigit (c : w8) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

instance : DecidablePred isDigit := fun c => by unfold isDigit; infer_instance

def isIdentByte (c : w8) : Prop :=
  isDigit c ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c.toNat = 45

instance : DecidablePred isIdentByte := fun c => by unfold isIdentByte; infer_instance

/-- A decimal of at most 9 digits without a leading zero. -/
def numOk (g : List w8) : Prop :=
  g ≠ [] ∧ g.length ≤ 9 ∧ (∀ c ∈ g, isDigit c) ∧ (g.length = 1 ∨ g.head? ≠ some (W8 48))

instance : DecidablePred numOk := fun g => by unfold numOk; infer_instance

/-- A prerelease identifier: non-empty, of letters, digits and `-`; numeric without a leading
zero. -/
def identOk (g : List w8) : Prop :=
  g ≠ [] ∧ (∀ c ∈ g, isIdentByte c) ∧
    ((∃ c ∈ g, ¬ isDigit c) ∨ g.length = 1 ∨ g.head? ≠ some (W8 48))

instance : DecidablePred identOk := fun g => by unfold identOk; infer_instance

/-- **A version of the simple form.** -/
def semverSimple (s : GoString) : Prop :=
  (splitBy (W8 46) (s.takeWhile (· ≠ W8 45))).length = 3 ∧
    (∀ g ∈ splitBy (W8 46) (s.takeWhile (· ≠ W8 45)), numOk g) ∧
    (s.dropWhile (· ≠ W8 45) = [] ∨
      ∀ g ∈ splitBy (W8 46) (s.dropWhile (· ≠ W8 45)).tail, identOk g)

instance : DecidablePred semverSimple := fun s => by unfold semverSimple; infer_instance

example : semverSimple go!"3.8.0-alpha.0" := by decide
example : semverSimple go!"2.0.0" := by decide
example : ¬ semverSimple go!"3.8.0-alpha..0" := by decide
example : ¬ semverSimple go!"3.8" := by decide
example : ¬ semverSimple go!"3.08.0" := by decide

/-- **The trust boundary**: a version of the simple form parses (`semver.NewVersion` accepts it,
so `semver.MustParse` returns a version). -/
axiom semverValid_simple (s : GoString) (h : semverSimple s) : apply.semverValid s

end semver
end EtcdGrove
end Perennial
