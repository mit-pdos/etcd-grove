/-
**What `semver.Version.Compare` computes** (prove-ps2-semver, 2026-11-22): a pure model of
semver v3.5.0's `Compare`, `compareSegment`, `comparePrerelease` and `comparePrePart`
(`version.go:525-730`), line for line, the results as Go's `int`s. The specs of those functions,
and of `LessThan` (`Compare(o) < 0`), return what these say. Lean-first.
-/
module

public import Proof.github_com.Masterminds.semver.v3.PkgInit
public import Perennial.Proof.strings.Base
public import Perennial.Proof.internal.strconv.ParseUintBasics

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace semver

section
variable [GooseExts]

/-- `compareSegment(v, o)`: `-1`, `1` or `0` as `v` is below, above or equal to `o`. -/
def cmpSeg (v o : w64) : w64 :=
  if uint.Z v < uint.Z o then W64 (-1) else if uint.Z o < uint.Z v then W64 1 else W64 0

/-- `comparePrePart(s, o)`: equal parts `0`; an empty part against a non-empty one; else two
numbers (`strconv.ParseUint(_, 10, 64)` without an error) by value, a number below a
non-number, two non-numbers by their bytes. -/
def cmpPrePart (s o : GoString) : w64 :=
  if s = o then W64 0
  else if s = [] then (if o ≠ [] then W64 (-1) else W64 1)
  else if o = [] then (if s ≠ [] then W64 1 else W64 (-1))
  else
    match internal.strconv.parseUint o 10 64, internal.strconv.parseUint s 10 64 with
    | .ok oi, .ok si => if uint.Z (W64 oi) < uint.Z (W64 si) then W64 1 else W64 (-1)
    | .ok _, _ => W64 1
    | _, .ok _ => W64 (-1)
    | _, _ => if go.GoStringLt o s then W64 1 else W64 (-1)

/-- `comparePrerelease`'s loop over the dot-separated parts, a missing part read as `""`: the
first non-zero `comparePrePart`, else `0`. -/
def cmpParts : List GoString → List GoString → w64
  | [], [] => W64 0
  | s :: ss, [] => if cmpPrePart s [] = W64 0 then cmpParts ss [] else cmpPrePart s []
  | [], o :: os => if cmpPrePart [] o = W64 0 then cmpParts [] os else cmpPrePart [] o
  | s :: ss, o :: os => if cmpPrePart s o = W64 0 then cmpParts ss os else cmpPrePart s o

/-- `comparePrerelease(v, o)`. -/
def cmpPre (v o : GoString) : w64 :=
  cmpParts (strings.split v go!".") (strings.split o go!".")

/-- **`v.Compare(o)`**: by major, minor and patch numbers, then a version without a prerelease
above one with, then the prereleases (`comparePrerelease`); the metadata is ignored. -/
def compare (x y : github_com.Masterminds.semver.v3.Version) : w64 :=
  if cmpSeg x.major' y.major' ≠ W64 0 then cmpSeg x.major' y.major'
  else if cmpSeg x.minor' y.minor' ≠ W64 0 then cmpSeg x.minor' y.minor'
  else if cmpSeg x.patch' y.patch' ≠ W64 0 then cmpSeg x.patch' y.patch'
  else if x.pre' = [] ∧ y.pre' = [] then W64 0
  else if x.pre' = [] then W64 1
  else if y.pre' = [] then W64 (-1)
  else cmpPre x.pre' y.pre'

/-- **`v.LessThan(o)`**: `v.Compare(o) < 0`. -/
def lessThan (x y : github_com.Masterminds.semver.v3.Version) : Prop :=
  sint.Z (compare x y) < 0

instance (x y : github_com.Masterminds.semver.v3.Version) : Decidable (lessThan x y) := by
  unfold lessThan; infer_instance

/-- One step of `cmpParts`, at index `i` of both lists while one of them has a part there. -/
theorem cmpParts_drop (a b : List GoString) (i : Nat) (h : i < a.length ∨ i < b.length) :
    cmpParts (a.drop i) (b.drop i) =
      if cmpPrePart (a[i]?.getD []) (b[i]?.getD []) = W64 0
      then cmpParts (a.drop (i + 1)) (b.drop (i + 1))
      else cmpPrePart (a[i]?.getD []) (b[i]?.getD []) := by
  have ha : ∀ (l : List GoString), l.drop i = (l[i]?.toList) ++ l.drop (i + 1) := by
    intro l
    rcases Nat.lt_or_ge i l.length with hl | hl
    · rw [List.getElem?_eq_getElem hl]
      rw [List.drop_eq_getElem_cons hl]; rfl
    · rw [List.getElem?_eq_none hl, List.drop_eq_nil_of_le hl,
        List.drop_eq_nil_of_le (by omega)]
      rfl
  rw [ha a, ha b]
  rcases Nat.lt_or_ge i a.length with hl | hl <;> rcases Nat.lt_or_ge i b.length with hm | hm
  · rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hm]
    simp only [Option.toList_some, List.singleton_append, Option.getD_some]
    rw [cmpParts]
  · rw [List.getElem?_eq_getElem hl, List.getElem?_eq_none hm,
      List.drop_eq_nil_of_le (show b.length ≤ i + 1 by omega)]
    simp only [Option.toList_some, Option.toList_none, List.singleton_append, List.nil_append,
      Option.getD_some, Option.getD_none]
    rw [cmpParts]
  · rw [List.getElem?_eq_none hl, List.getElem?_eq_getElem hm,
      List.drop_eq_nil_of_le (show a.length ≤ i + 1 by omega)]
    simp only [Option.toList_some, Option.toList_none, List.singleton_append, List.nil_append,
      Option.getD_some, Option.getD_none]
    rw [cmpParts]
  · omega

/-- `cmpParts` past both lists. -/
theorem cmpParts_drop_end (a b : List GoString) (i : Nat) (h : a.length ≤ i ∧ b.length ≤ i) :
    cmpParts (a.drop i) (b.drop i) = W64 0 := by
  rw [List.drop_eq_nil_of_le h.1, List.drop_eq_nil_of_le h.2, cmpParts]

end

end semver
end EtcdGrove
end Perennial
