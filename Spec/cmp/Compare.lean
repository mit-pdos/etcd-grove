/-
`cmp.Compare` at `int64` (sortslice, 2026-11-24: `mvcc.hashStorage.Store`'s comparator,
`cmp.Compare(a.Revision, b.Revision)`, over the fork's `slices.SortFunc`). Perennial translates `cmp`
with its bodies but states no spec of `Compare` (`notes/perennial-changes.md`: to move there).
Lean-first.
-/
module

public import Perennial.Proof.cmp.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.cmp.Assumptions]

/-- `cmp.Compare(x, y)` at `int64` is `-1`, `0` or `+1` as `x` is less than, equal to or greater
than `y` (an integer is never a NaN). -/
abbrev cmp.Compare.spec : Prop :=
  ∀ (x y : w64),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions _root_.Perennial.cmp.Compare [go.int64])) (Val #x)) (Val #y))
    {{ (r : w64), RET #r;
        ⌜r = if sint.Z x < sint.Z y then W64 (-1) else if sint.Z y < sint.Z x then W64 1 else W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
