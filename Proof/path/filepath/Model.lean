/-
**`filepath.Ext`, as a pure function** (WAL leaf specs, 2026-11-13; `fileutil.ReadDir`'s extension
filter). The other lexical functions of `path/filepath` on Unix compute exactly `path`'s, whose
models are the main tree's `Proof/path/Model.lean` (`cleanModel`, `joinModel`, `baseModel`,
`dirModel`). Lean-first.

`Ext(p)`: `for i := len(p) - 1; i >= 0 && p[i] != '/'; i-- { if p[i] == '.' { return p[i:] } }`,
then `""`: the suffix of `p` from the last `.` of its last element, or empty.
-/
module

public import Proof.path.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace filepath

open path

/-- `Ext`'s loop from `i` down (exclusive): the suffix from the last `.` below `i` that no `/`
follows, or `[]`. -/
def extFrom (p : List w8) : Nat → List w8
  | 0 => []
  | i + 1 => if p.getD i 0 = slash then [] else if p.getD i 0 = dot then p.drop i else extFrom p i

/-- `Ext(p)`. -/
def extModel (p : List w8) : List w8 := extFrom p p.length

example : extModel go!"000000000000000a-0000000000000001.wal" = go!".wal" := by
  decide
example : extModel go!"/a.b/c" = [] := by decide
example : extModel go!"x.tar.gz" = go!".gz" := by decide

end filepath
end EtcdGrove
end Perennial
