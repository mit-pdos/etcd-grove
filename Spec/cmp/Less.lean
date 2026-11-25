/-
`cmp.Less` at `int64` (sortslice2, 2026-11-25: `slices.Sort` of an `[]int64`, mvccrand's
`writer.genLease`) and at `int32` (dsv-fix4, 2026-11-25: gryff's `gryffcommon.ShortCircuit` sorts
its `[]int32` with `slices.Sort`). Perennial translates `cmp` with its bodies and specifies `Less` only at `uint64`
and `string` (`Perennial/Spec/cmp/Less.lean`; `notes/perennial-changes.md`: to move there).
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

/-- `cmp.Less(x, y)` at `int64` is `<` on the signed values (an integer is never a NaN). -/
abbrev cmp.Less.spec : Prop :=
  ∀ (x y : w64),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions _root_.Perennial.cmp.Less [go.int64])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ sint.Z x < sint.Z y⌝ }}

/-- `cmp.Less(x, y)` at `int32` is `<` on the signed values. -/
abbrev cmp.Less.specInt32 : Prop :=
  ∀ (x y : w32),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions _root_.Perennial.cmp.Less [go.int32])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ sint.Z x < sint.Z y⌝ }}

end spec

end EtcdGrove
end Perennial
