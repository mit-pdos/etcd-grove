/-
The path vocabulary of the abstract-disk extension [Trusted definitions!] (WAL W4a revision after
the Freeze review, 2026-11-11; `notes/decisions.md`, "WAL W4a revision").

Paths are strings (`GoString`). The WAL directories lie in one fixed directory, the WAL area
(`AbsDiskState.area`), each a single element `area/n` (`walAreaDir`); the durable extension's names
and `TouchDirAll`'s directories lie outside it (`underDir`). Clean absolute paths (`cleanAbsPath`)
are those Go's `filepath.Clean` leaves unchanged, so `filepath.Clean(dir) + ".tmp"` is
`dir ++ ".tmp"` and `filepath.Dir(r ++ "/" ++ n)` is `r`. That distinct strings name distinct files
(no symbolic link on the paths a run uses) is a world assumption (`Impl.lean`).
-/
module

public import Perennial.Golang.Defn.PostLang

@[expose] public section

namespace Perennial

/-- **An element of a clean path**: nonempty, no `/`, neither `.` nor `..`. -/
def pathElemOk (c : GoString) : Prop :=
  c ≠ [] ∧ W8 47 ∉ c ∧ c ≠ go!"." ∧ c ≠ go!".."

/-- **A clean absolute path other than `/`**: `/c₁/…/cₙ` (`n ≥ 1`), each `cᵢ` an element. Go's
`filepath.Clean` leaves it unchanged; `filepath.Dir (p ++ "/" ++ c)` is `p` for an element `c`. -/
def cleanAbsPath (p : GoString) : Prop :=
  ∃ cs : List GoString, cs ≠ [] ∧ (∀ c ∈ cs, pathElemOk c) ∧ p = (cs.map (go!"/" ++ ·)).flatten

/-- **`p` lies strictly under the directory `r`**. -/
def underDir (r p : GoString) : Prop := (r ++ go!"/") <+: p

/-- **A WAL directory's name**: nonempty, without `/` or `.` (so never a `Create`'s `n.tmp`, a
cleanup's `n.broken.*`, nor `.` or `..`). -/
def walNameOk (n : GoString) : Prop := n ≠ [] ∧ W8 47 ∉ n ∧ W8 46 ∉ n

/-- **`dir` is a WAL directory of the area `r`**: `r/n`, `n` a WAL name. -/
def walAreaDir (r dir : GoString) : Prop := ∃ n, walNameOk n ∧ dir = r ++ go!"/" ++ n

/-- **What `Create(dir)` removes** (S/wal.go:113-118, 323): `dir` and what is under it (`renameWAL`'s
`RemoveAll(dir)`), `dir.tmp` and what is under it (`RemoveAll(filepath.Clean(dir)+".tmp")`, `dir`
clean). -/
def walCreateRegion (dir k : GoString) : Prop :=
  k = dir ∨ underDir dir k ∨ k = dir ++ go!".tmp" ∨ underDir (dir ++ go!".tmp") k

end Perennial
