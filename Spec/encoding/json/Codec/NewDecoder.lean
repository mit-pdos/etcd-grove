/-
`json.NewDecoder(r)` over the encoding/json model (`models/encoding/json/v2_stream.go`): a non-nil
reader `r` gives a healthy decoder reading it, which has read nothing (`DecoderRep.decOk` at
`R = U = []`, with the stream's resource `I []`). Proved at the model's decoder (`decRepModel`):
`Proof/encoding/json/Codec/NewDecoder.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [DecoderRep GF]

/-- `NewDecoder(r)`, `r` non-nil: a healthy decoder reading `r`, nothing read. -/
abbrev NewDecoder.spec : Prop :=
  ∀ (r : GoInterface) (I : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ ⌜r ≠ interface.nil⌝ ∗ I [] }}
    (App (Val (@! encoding.json.NewDecoder)) (Val #r))
  {{ (dec : Loc), RET #dec; DecoderRep.decOk (GF := GF) dec r I [] [] }}

end spec

end encoding.json
end Perennial
