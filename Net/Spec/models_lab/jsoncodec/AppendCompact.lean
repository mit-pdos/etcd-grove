/-
`jsoncodec.AppendCompact(b, raw)` on one complete value (`Scan` ends at its end) that `AppendCompact`
keeps as it is (`cmpRun`, `Compact.lean`: no whitespace outside strings, no byte it rejects inside
them; what a generated encoder writes): `raw` appended, `true`. Proved in
`Net/Proof/models_lab/jsoncodec/AppendCompact.lean`; ported from dsverify-lab's `wp_AppendCompact_ok`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Compact

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
abbrev AppendCompact.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (raw : GoSlice) (dq : DFrac) (rs : List w8)
    (hsc : JsonScan.scanL rs true = (0, rs.length)) (hc : cmpRun false rs = some false),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ raw ↦*{dq} rs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.AppendCompact)) (Val #b)) (Val #raw))
  {{ (b' : GoSlice), RET (PairV #b' #true); b' ↦* (bs ++ rs) ∗
      ownSliceCap w8 b' (DFrac.own 1) ∗ raw ↦*{dq} rs }}

end spec

end models_lab.jsoncodec
end Perennial
