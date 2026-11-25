/-
`jsoncodec.Valid(b)` on one complete value with nothing after it (`Scan` ends at the end):
`true`. Proved in `Net/Proof/models_lab/jsoncodec/Valid.lean`; ported from dsverify-lab's
`wp_Valid_ok` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits
public import Net.Proof.models_lab.jsoncodec.Scan.Idx

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
abbrev Valid.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8)
    (hsc : JsonScan.scanL bs true = (0, bs.length)),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (Val (@! models_lab.jsoncodec.Valid)) (Val #b))
  {{ RET #true; b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
