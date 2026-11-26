/-
`token.IsExported(name)` (the model, `models/go/token/model.go`, until 2026-11-24 `Net/TrustedCode/go/token.lean`) on a name whose first byte is
an upper-case ASCII letter: `true` (Go's `unicode.IsUpper` fast path). Proved in
`Net/Proof/go/token/IsExported.lean`.
-/
module

public import Net.GeneratedProof.go.token

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace go.token

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : go.token.Assumptions]

/-- See the file header. -/
abbrev IsExported.spec : Prop :=
  ∀ (c : w8) (rest : GoString), uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ (True : IProp GF) }}
    (App (Val (@! go.token.IsExported)) (Val #(c :: rest)))
  {{ RET #true; True }}

end spec

end go.token
end Perennial
