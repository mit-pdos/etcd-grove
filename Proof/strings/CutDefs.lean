/-
**What Go's `strings.Index`, `strings.Cut` and `strings.TrimLeft` return**, as pure functions (the
vocabulary of `Spec/strings/Cut.lean` and `Spec/strings/TrimLeft.lean`; Go 1.27.3, `strings.go` and
`internal/stringslite`). Lean-first.

* `strings.index s sep`: the first `i` at which `sep` occurs in `s` (`sep` a prefix of `s.drop i`), or
  `none` (Go's `-1`); `0` for an empty `sep`.
* `strings.cut s sep`: `Cut(s, sep)`, `s[:i], s[i+len(sep):], true` at that `i`, else `s, "", false`.
* `strings.trimLeft s cutset`: `TrimLeft(s, cutset)` for an ASCII `cutset` (every byte below `0x80`:
  Go's `trimLeftByte` or `trimLeftASCII`, a byte loop), `s` without its leading bytes in `cutset`. A
  cutset with a non-ASCII byte is trimmed rune by rune (`trimLeftUnicode`), which this does not state.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- See the file header. -/
def strings.index (s sep : GoString) : Option Nat :=
  (List.range (s.length + 1)).find? (fun i => decide (sep <+: s.drop i))

/-- See the file header. -/
def strings.cut (s sep : GoString) : GoString × GoString × Bool :=
  match strings.index s sep with
  | some i => (s.take i, s.drop (i + sep.length), true)
  | none => (s, [], false)

/-- See the file header. -/
def strings.trimLeft (s cutset : GoString) : GoString :=
  s.dropWhile (fun b => decide (b ∈ cutset))

end EtcdGrove
end Perennial
