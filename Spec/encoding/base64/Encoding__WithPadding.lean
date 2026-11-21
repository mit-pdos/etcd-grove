/-
`(Encoding).WithPadding(padding)` (`encoding/base64`, go1.27.3 `base64.go`), called through a pointer,
for `NoPadding`: a fresh `*Encoding`, a copy of `*e` without padding. Proved in
`Proof/encoding/base64/Encoding__WithPadding.lean`. Lean-first.
-/
module

public import Proof.encoding.base64.Defs

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
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

/-- `e.WithPadding(NoPadding)`: a copy of `*e` whose `padChar` is `NoPadding` (`-1`). -/
abbrev base64.Encoding.WithPadding.spec : Prop :=
  ∀ (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dqe : DFrac),
  {{ (e ↦{dqe} enc : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType _root_.Perennial.encoding.base64.Encoding.ty @!!
      go!"WithPadding")) (Val _root_.Perennial.encoding.base64.NoPadding))
  {{ (e' : Loc), RET #e'; e ↦{dqe} enc ∗ e' ↦ { enc with padChar' := W32 (-1) } }}

end spec

end EtcdGrove
end Perennial
