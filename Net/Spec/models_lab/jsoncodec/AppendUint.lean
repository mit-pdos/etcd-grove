/-
`jsoncodec.AppendUint(b, x)`: `b` with the decimal digits of `x` (`JsonScan.decN`) after it (a
slice with its capacity, owned whole). Proved in `Net/Proof/models_lab/jsoncodec/AppendUint.lean`;
ported from dsverify-lab's `wp_AppendUint` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoEnc.lean`,
lab master 915f964).
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
abbrev AppendUint.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (x : w64),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.AppendUint)) (Val #b)) (Val #x))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ JsonScan.decN (uint.nat x)) ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.jsoncodec
end Perennial
