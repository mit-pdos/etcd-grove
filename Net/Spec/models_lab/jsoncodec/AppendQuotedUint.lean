/-
`jsoncodec.AppendQuotedUint(b, x)`: `b` with `"`, the decimal digits of `x`, `"` after it.
Proved in `Net/Proof/models_lab/jsoncodec/AppendQuotedUint.lean`; ported from dsverify-lab's
`wp_AppendQuotedUint` (`GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev AppendQuotedUint.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (x : w64),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.AppendQuotedUint)) (Val #b)) (Val #x))
  {{ (b' : GoSlice), RET #b';
      b' ↦* (bs ++ (34#8 :: (JsonScan.decN (uint.nat x) ++ [34#8]))) ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.jsoncodec
end Perennial
