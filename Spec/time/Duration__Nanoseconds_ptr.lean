/-
`(*time.Duration).Nanoseconds()`: the trust boundary (Perennial translates `time` without
`Duration`'s methods; `func (d Duration) Nanoseconds() int64 { return int64(d) }`, called through
the pointer of an addressable `Duration`, as client-go's exponential limiter's `r.baseDelay`).
Lean-first.
-/
module

public import Perennial.Proof.time

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

/-- `l.Nanoseconds()` on the `Duration` `*l = d`: `d` as an `int64` (its bits). -/
abbrev time.Duration.Nanoseconds_ptr.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ l ↦{dq} d }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Duration.ty @!! go!"Nanoseconds"))
      (Val #()))
  {{ RET #(d : w64); l ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
