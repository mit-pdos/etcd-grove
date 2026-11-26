/-
`wire.RandomInt` and `wire.RandomBytes` linked to Goose's `primitive.RandomUint64`
(`Perennial/Proof/github_com/goose_lang/primitive/Link.lean`), for the examples' linking modules.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomInt
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomBytes
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

theorem wp_RandomInt : RandomInt.spec (GF := GF) (hG := hG) :=
  RandomInt.wp_proof github_com.goose_lang.primitive.wp_RandomUint64

theorem wp_RandomBytes : RandomBytes.spec (GF := GF) (hG := hG) :=
  RandomBytes.wp_proof github_com.goose_lang.primitive.wp_RandomUint64

end link

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
