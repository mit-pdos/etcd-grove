/-
`b.Grow(n)` on a zero `strings.Builder` (`var b strings.Builder`), for `n ≥ 0` (Go's `builder.go`:
`copyCheck`, then the negative-count panic, then `grow(n)`, which allocates `MakeNoZero(2*cap(b.buf)+n)`
and copies the buffer's bytes, none here): the Builder has accumulated `""`. Stated for a zero Builder
only: on one with capacity `c`, `2*c + n` may overflow `int`, and `strings.ownBuilder` does not say
`c`. Pending: Perennial translates `Builder.Grow` with its body but has no spec of it at the pin (nor
of `bytealg.MakeNoZero`'s model, which `grow` calls), `notes/perennial-changes.md`. No proof file: the
Links that reach it take this spec as a hypothesis. Lean-first (phase 7 S5, `url.unescape`, 2026-11-24).
-/
module

public import Perennial.Proof.strings.BuilderBasics

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
variable [package_sem : _root_.Perennial.strings.Assumptions]

/-- See the file header. -/
abbrev strings.Builder.Grow.spec : Prop :=
  ∀ (l : Loc) (n : w64), 0 ≤ sint.Z n →
    {{ l ↦ (zero_val _root_.Perennial.strings.Builder) }}
      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.strings.Builder.ty @!! go!"Grow"))
        (Val #n))
    {{ RET #(); _root_.Perennial.strings.ownBuilder (GF := GF) l [] }}

end spec

end EtcdGrove
end Perennial
