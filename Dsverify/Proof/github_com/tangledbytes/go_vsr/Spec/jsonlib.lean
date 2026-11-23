/-
The vocabulary of the future `encoding/json` hypotheses (notes/dsv-vr.md, "Hypotheses"): the
definitions the vr hubs state their specs in, where the lab had them from its own `encoding/json`
and `bufio` models (`Harness/Proof/encoding/json/{json,Defs}.lean`, `Harness/Proof/bufio/Defs.lean`,
lab master 915f964). **Definitions only**: no spec of an `encoding/json` function is stated or
assumed here; the hypotheses (`Marshal.spec`, `Unmarshal.spec`, `NewEncoder.spec`,
`Encoder.Encode.spec`, `NewDecoder.spec`, `Decoder.Decode.spec`, ...) will be stated over these
names when they are needed. Names are the lab's.

* The codec (`JsonCodec`, `jsonValid`, `marshalOk`, `unmarshalOk`, `scanOk`, `scanFn`) is the
  repository's (`Net/Proof/models_lab/jsoncodec/Codec.lean`, ported from the lab's
  `Harness/Proof/encoding/json/Defs.lean`); here only what the lab had beyond it: `kitFn` (the kit's
  generated functions: `jsonMarshal`, `jsonUnmarshal` in `examples/vsrnet`, which jsongen will
  write, notes/dsv-vr.md finding 2; the lab's `JsonKit.pkg` is that package's path),
  `kitCodecOk F`, `codecFns c` and `codecSet` (over the model's `codec` and `Codec` fields, as the
  lab's model: `models/encoding/json/model.go`), `isSpaceB` (the model's `isSpace`).
* **The decoder** (`DecoderRep`): the model's `Decoder` is translated names only (an opaque type:
  its fields cannot be named here), so its representation predicate is a class: `decOk dec rd I R U`
  (healthy: `dec` reads the `io.Reader` `rd`, from which it has read `R`, holding the underlying
  stream's resource `I R`, as bufio's `readerOk rd I`; `U`, a suffix of `R`, its unread bytes) and
  `decErr dec rd` (its sticky error is set: every `Decode` returns it). The lab's `events.rstream`
  read the lab model's fields (`buf`, `scanp`, `err`, `rerr`); these two stand for them. An instance
  is the model's choice, given with the decoder's specs; none is given here.
* `bufio.errWf`, `bufio.errOrNil`: an error result (nil, or an error with some message), over the
  repository's `models_lab.errAny` (the lab's `net.rpc.errAny`).
-/
module

public import Dsverify.Proof.encoding.json.Base
public import Net.Proof.models_lab.jsoncodec.Codec
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- JSON whitespace (`isSpace` in the model; the codec's `models_lab.jsoncodec.spaceB`). -/
def isSpaceB (c : w8) : Bool :=
  [W8 32, W8 9, W8 10, W8 13].contains c

theorem isSpaceB_spaceB (c : w8) : isSpaceB c = models_lab.jsoncodec.spaceB c := rfl

/-- The package of the kit's generated codec functions (the lab's `JsonKit.pkg`). -/
def kitPkg : GoString := go!"github.com/tangledbytes/go-vsr/examples/vsrnet"

/-- The kit's generated function `name` (in `kitPkg`). -/
def kitFn [GooseExts] [GoSemanticsFunctions] (name : GoString) : GoFunc :=
  functions (kitPkg ++ go!"." ++ name) []

/-- The representation of the model's `*Decoder` (see the file header; no instance here). -/
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

/-- The kit's codec functions meet `JsonCodec`, and `jsoncodec.Scan` computes `F` (persistent). -/
def kitCodecOk (F : List w8 → Bool → w64 × w64) : IProp GF :=
  iprop(models_lab.jsoncodec.marshalOk (kitFn go!"jsonMarshal") ∗
    models_lab.jsoncodec.unmarshalOk F (kitFn go!"jsonUnmarshal") ∗
    models_lab.jsoncodec.scanOk F models_lab.jsoncodec.scanFn)

instance kitCodecOk_persistent F : Persistent (kitCodecOk (GF := GF) F) := by
  unfold kitCodecOk; infer_instance

end defs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- The `*Codec` `c` holds the kit's codec functions, for good (persistent). -/
def codecFns (c : Loc) : IProp GF :=
  iprop(structFieldRef encoding.json.Codec go!"Marshal" c ↦□ kitFn go!"jsonMarshal" ∗
    structFieldRef encoding.json.Codec go!"Unmarshal" c ↦□ kitFn go!"jsonUnmarshal" ∗
    structFieldRef encoding.json.Codec go!"Scan" c ↦□ models_lab.jsoncodec.scanFn)

instance codecFns_persistent (c : Loc) : Persistent (codecFns (GF := GF) c) := by
  unfold codecFns; infer_instance

/-- A codec with the kit's functions is registered, for good (persistent). -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.json.codec ↦□ c ∗ codecFns c)

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

end defs2

end encoding.json

namespace bufio

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A non-nil error of a pointer type holds a pointer (true of every error Go code makes; what
comparing it with an `errors.New` error needs). -/
def errWf [GooseExts] [GoGlobalContext] (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → ∀ T : go.GoType, e.ty = go.GoType.PointerType T →
    ∃ l : Loc, e.v = #l

/-- An error result: `nil`, or an error with some message (and `errWf`). -/
def errOrNil (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (models_lab.errAny err ∗ ⌜errWf err⌝))

instance errOrNil_persistent (err : GoInterface) : Persistent (errOrNil (GF := GF) err) := by
  unfold errOrNil; infer_instance

end defs

end bufio

end Perennial
