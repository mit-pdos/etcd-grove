/-
`jsoncodec.Scan(b, eof)`: `JsonScan.scanF bs eof` (the Lean scanner, `Scan/Def.lean`), for any
input (it never panics). Proved in `Net/Proof/models_lab/jsoncodec/Scan.lean`; ported from
dsverify-lab's `wp_Scan` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoScan.lean`, lab master
915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Def

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
abbrev Scan.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (eof : Bool),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.Scan)) (Val #b)) (Val #eof))
  {{ RET (PairV #(JsonScan.scanF bs eof).1 #(JsonScan.scanF bs eof).2); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
