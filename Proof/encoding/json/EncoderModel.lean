/-
The model's `*Encoder` (`models/encoding/json/v2_stream.go`, translated with its bodies: `NewEncoder`,
`Encoder.Encode`) as an `EncoderRep` (`Registry.lean`), over its fields: `encOkModel enc w`, `enc`
points to an `Encoder` writing to `w`, its sticky error nil and no indentation (what
`NewEncoder(w)` builds, `&Encoder{w: w, escapeHTML: true}`). `encRepModel` is that representation;
the proofs of `NewEncoder.spec` and `Encoder.Encode_conn.spec` at it are
`Codec/NewEncoder.lean`, `Codec/Encoder__Encode_conn.lean`. Definitions only. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [encoding.json.Assumptions]

/-- A healthy `*Encoder` writing to `w` (see the file header). -/
def encOkModel (enc : Loc) (w : GoInterface) : IProp GF :=
  iprop(∃ e : encoding.json.Encoder, enc ↦ e ∗
    ⌜e.w' = w ∧ e.err' = interface.nil ∧ e.indentPrefix' = zero_val GoString ∧
      e.indentValue' = zero_val GoString⌝)

/-- The model's encoder representation (at this heap). -/
@[instance_reducible] def encRepModel : EncoderRep GF := ⟨encOkModel (hG := hG)⟩

theorem encRepModel_encOk (enc : Loc) (w : GoInterface) :
    (encRepModel (hG := hG)).encOk enc w = encOkModel (hG := hG) enc w := rfl

end defs

end encoding.json
end Perennial
