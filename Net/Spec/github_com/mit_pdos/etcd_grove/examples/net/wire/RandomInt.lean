/-
`wire.RandomInt(max)`, for `max` in `[0, 2^31)`: a number drawn at random (Goose's
`primitive.RandomUint64`, modulo `max + 1`) in `[0, max]`. Proved in
`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/wire/RandomInt.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

/-- See the file header. -/
abbrev RandomInt.spec : Prop :=
  ∀ (max : w64),
  {{ (⌜0 ≤ sint.Z max ∧ sint.Z max < 2 ^ 31⌝ : IProp GF) }}
    (App (Val (@! wire.RandomInt)) (Val #max))
  {{ (k : w64), RET #k; ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z max⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
