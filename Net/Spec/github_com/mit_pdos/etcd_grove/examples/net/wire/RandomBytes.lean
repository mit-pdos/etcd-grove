/-
`wire.RandomBytes(n)`, for `n ≥ 0`: a new slice of `n` bytes, each drawn at random (Goose's
`primitive.RandomUint64`); the caller owns it. Nothing is said of the bytes: the examples' checks
hold for every request. Proved in
`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/wire/RandomBytes.lean`.
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
abbrev RandomBytes.spec : Prop :=
  ∀ (n : w64),
  {{ (⌜0 ≤ sint.Z n⌝ : IProp GF) }}
    (App (Val (@! wire.RandomBytes)) (Val #n))
  {{ (b : GoSlice), RET #b; ∃ bs : List w8, b ↦* bs ∗ ⌜bs.length = sint.nat n⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
