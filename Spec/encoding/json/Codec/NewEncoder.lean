/-
`json.NewEncoder(w)` over the encoding/json model (mit-pdos/etcd-grove#24, item 1): an encoder
writing to `w`, healthy (`EncoderRep.encOk`, a class while the model's bodies are opaque). Moved from
`Dsverify`'s vr kit (`encoding.json.NewEncoder.spec`, the lab's `Harness/Proof/encoding/json/
Stream.lean`). A statement only: neither assumed nor proved yet (the model's `NewEncoder` is
`&Encoder{w: w}`). Lean-first (no Rocq counterpart).
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
variable [EncoderRep GF]

/-- `NewEncoder(w)`: a healthy encoder writing to `w`. -/
abbrev NewEncoder.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json }}
    (App (Val (@! encoding.json.NewEncoder)) (Val #w))
  {{ (enc : Loc), RET #enc; EncoderRep.encOk (GF := GF) enc w }}

end spec

end encoding.json
end Perennial
