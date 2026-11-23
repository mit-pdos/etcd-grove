/-
The encoding/json model's codec registry, as the specs over it see it (mit-pdos/etcd-grove#24,
item 1): the main tree's `encoding/json` is the model's (`models/encoding/json`, std_models; names
only for now), whose `Marshal`, `Unmarshal`, `Encoder.Encode` and `Decoder.Decode` call the codec the
program registered with `SetCodec` (`model.go`: the package variable `codec`, a `*Codec` of three
functions). Definitions only: no spec of an `encoding/json` function is stated or assumed here.

Generic over the program's generated functions (`jsongen.py`'s `jsonMarshal`, `jsonUnmarshal`, in the
program's own package): a kit names them (vr's `codecSet` is `codecSetWith (kitFn "jsonMarshal")
(kitFn "jsonUnmarshal")`, `Dsverify`'s `Spec/jsonlib.lean`, from which these are moved).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Base
public import Net.Proof.models_lab.jsoncodec.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- JSON whitespace (the model's `isSpace`; the codec's `models_lab.jsoncodec.spaceB`). -/
def isSpaceB (c : w8) : Bool :=
  [W8 32, W8 9, W8 10, W8 13].contains c

theorem isSpaceB_spaceB (c : w8) : isSpaceB c = models_lab.jsoncodec.spaceB c := rfl

/-- The representation of the model's `*Encoder` while the bodies are opaque (no instance is given;
the specs over it are hypotheses): `encOk enc w`, a healthy encoder (no sticky error) writing to
`w`. A definition over the model's fields once its bodies are translated. -/
class EncoderRep [GooseExts] (GF : BundledGFunctors) where
  encOk : Loc → GoInterface → IProp GF

/-- The representation of the model's `*Decoder` while the bodies are opaque (no instance is given):
`decOk dec rd I R U` (healthy: `dec` reads the `io.Reader` `rd`, from which it has read `R`, holding
the underlying stream's resource `I R`; `U`, a suffix of `R`, its unread bytes) and `decErr dec rd`
(its sticky error is set: every `Decode` returns it). Definitions over the model's fields (`buf`,
`prevEnd`, `err`, ...) once its bodies are translated. -/
class DecoderRep [GooseExts] (GF : BundledGFunctors) where
  /-- healthy: reading `rd` (stream resource `I`), read `R`, unread `U` -/
  decOk : Loc → GoInterface → (List w8 → IProp GF) → List w8 → List w8 → IProp GF
  /-- its sticky error is set -/
  decErr : Loc → GoInterface → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [jc : models_lab.jsoncodec.JsonCodec GF]

/-- The program's codec functions `fm`, `fu` meet `JsonCodec`, and `jsoncodec.Scan` computes `F`
(persistent). -/
def codecOkWith (F : List w8 → Bool → w64 × w64) (fm fu : GoFunc) : IProp GF :=
  iprop(models_lab.jsoncodec.marshalOk fm ∗ models_lab.jsoncodec.unmarshalOk F fu ∗
    models_lab.jsoncodec.scanOk F models_lab.jsoncodec.scanFn)

instance codecOkWith_persistent F fm fu : Persistent (codecOkWith (GF := GF) F fm fu) := by
  unfold codecOkWith; infer_instance

end defs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- The `*Codec` `c` holds the functions `fm`, `fu` and `jsoncodec.Scan`, for good (persistent). -/
def codecFnsWith (fm fu : GoFunc) (c : Loc) : IProp GF :=
  iprop(structFieldRef encoding.json.Codec go!"Marshal" c ↦□ fm ∗
    structFieldRef encoding.json.Codec go!"Unmarshal" c ↦□ fu ∗
    structFieldRef encoding.json.Codec go!"Scan" c ↦□ models_lab.jsoncodec.scanFn)

instance codecFnsWith_persistent fm fu (c : Loc) :
    Persistent (codecFnsWith (GF := GF) fm fu c) := by
  unfold codecFnsWith; infer_instance

/-- A codec of the functions `fm`, `fu` is registered, for good (persistent): `SetCodec` was
called with it, and the model's `codec` is never written again (a second `SetCodec` panics). -/
def codecSetWith (fm fu : GoFunc) : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.json.codec ↦□ c ∗ codecFnsWith fm fu c)

instance codecSetWith_persistent fm fu : Persistent (codecSetWith (GF := GF) fm fu) := by
  unfold codecSetWith; infer_instance

end defs2

end encoding.json
end Perennial
