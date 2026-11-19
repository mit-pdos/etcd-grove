/-
`jsoncodec.AppendRaw(b, s)`: `b` with `s`'s bytes after it (a slice with its capacity, owned
whole). Proved in `Net/Proof/netmodels_lab/jsoncodec/AppendRaw.lean`; ported from dsverify-lab's
`wp_AppendRaw` (`Harness/Proof/jsoncodec/Helpers.lean`, `348a866`).
-/
module

public import Net.Proof.netmodels_lab.jsoncodec.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace netmodels_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : netmodels_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev AppendRaw.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (str : GoString),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! netmodels_lab.jsoncodec.AppendRaw)) (Val #b)) (Val #str))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ str) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end netmodels_lab.jsoncodec
end Perennial
