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
public import Perennial.Proof.sync.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- JSON whitespace (the model's `isSpace`; the codec's `models_lab.jsoncodec.spaceB`). -/
def isSpaceB (c : w8) : Bool :=
  [W8 32, W8 9, W8 10, W8 13].contains c

/-- The number of JSON whitespace bytes at the start of `bs` (the model's `skipSpace`). -/
def leadSpace (bs : List w8) : Nat := (bs.takeWhile (fun c => isSpaceB c)).length

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

/-- `codecMu`'s invariant: half of `codec`'s points-to (as net/rpc's `codecInv`). -/
def codecInv : IProp GF :=
  iprop(∃ c : Loc, typedPointsto (globalAddr encoding.json.codec) c (DFrac.own (1 : Qp).half))

/-- No codec is registered yet (the package's initial state): the other half, at `nil`. What a
deployment that registers a codec takes from its boot, with `codecMu`'s mutex. -/
def codecUnset : IProp GF :=
  typedPointsto (globalAddr encoding.json.codec) null (DFrac.own (1 : Qp).half)

/-- A codec of the functions `fm`, `fu` is registered, for good (persistent): `SetCodec` was
called with it, and the model's `codec` is never written again (a second `SetCodec` is stuck: `stuck`, not modelled). With
the registry's mutex, which `getCodec` locks (#24 J2: J1's form had only the points-to). -/
def codecSetWith (fm fu : GoFunc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (globalAddr encoding.json.codecMu) codecInv ∗
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.json.codec ↦□ c ∗ codecFnsWith fm fu c)

instance codecSetWith_persistent fm fu : Persistent (codecSetWith (GF := GF) fm fu) := by
  unfold codecSetWith; infer_instance

end defs2

/-! ## The per-type dispatch (#24 J3)

`Marshal`, `Unmarshal`, `Encoder.Encode` and `Decoder.Decode` call a value's own
`JSONModelMarshalPtr`/`JSONModelMarshal`/`JSONModelUnmarshal` (jsongen's same-package methods) when
its dynamic type has them, and the registered codec otherwise (`model.go`, `marshalAny`). The
contract a call meets is `J : JsonCodec GF`, passed explicitly: a per-type route uses its type's
own (`typeCodecOk J F T`, a theorem of `T`'s package), the codec route the program's. -/

section dispatch
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

open models_lab.jsoncodec in
/-- `f` is `Marshal` at `v` for `J`: what `marshalOk` says of a codec's function, at one argument. -/
def marshalAt (J : JsonCodec GF) (f : val) (v : GoInterface) : IProp GF :=
  iprop(∀ (Ψ : Option (List w8) → IProp GF) (Φ : val → IProp GF),
    J.enc v Ψ -∗
    ▷ ((∀ (s : GoSlice) (bs : List w8), s ↦* bs -∗ ownSliceCap w8 s (DFrac.own 1) -∗
          Ψ (some bs) -∗ Φ (PairV #s #(interface.nil : GoInterface))) ∧
       (∀ (s : GoSlice) (err : GoInterface), ⌜err ≠ interface.nil⌝ -∗ Ψ none -∗
          Φ (PairV #s #err))) -∗
    WP (App (Val f) (Val #v)) {{ Φ }})

open models_lab.jsoncodec in
/-- `f` is `Unmarshal` at `ptr` for `J`, on any bytes (their validity by the scanner `F`): valid,
`J`'s decoding (`err` nil exactly when it decoded); else an error, nothing decoded. -/
def unmarshalAt (J : JsonCodec GF) (F : List w8 → Bool → w64 × w64) (f : val) (ptr : GoInterface) :
    IProp GF :=
  iprop(∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗ J.dec bs ptr Ψ -∗
    ▷ (∀ err : GoInterface, data ↦*{dq} bs -∗
        ((⌜jsonValid F bs⌝ ∗ ∃ ok, ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok) ∨
         (⌜¬ jsonValid F bs ∧ err ≠ interface.nil⌝ ∗ J.dec bs ptr Ψ)) -∗ Φ #err) -∗
    WP (App (App (Val f) (Val #data)) (Val #ptr)) {{ Φ }})

/-- What `Marshal(v)` returns, with `J.enc v Ψ`'s outcome: no error and the encoding `bs` in a
fresh slice `s` (its capacity owned), with `Ψ (some bs)`; or an error with `Ψ none`. -/
def marshalRet (Ψ : Option (List w8) → IProp GF) (s : GoSlice) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ bs : List w8, s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      Ψ (some bs)) ∨ (⌜err ≠ interface.nil⌝ ∗ Ψ none))

open models_lab.jsoncodec in
/-- What `Unmarshal(data, ptr)` returns (`data` holding `bs`), with `J.dec bs ptr Ψ`'s outcome:
valid JSON, `J`'s decoding (`err` nil exactly when it decoded); else an error, nothing decoded. -/
def unmarshalRet (J : JsonCodec GF) (F : List w8 → Bool → w64 × w64) (bs : List w8)
    (ptr : GoInterface) (Ψ : Bool → IProp GF) (err : GoInterface) : IProp GF :=
  iprop((⌜jsonValid F bs⌝ ∗ ∃ ok, ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok) ∨
    (⌜¬ jsonValid F bs ∧ err ≠ interface.nil⌝ ∗ J.dec bs ptr Ψ))

/-- **The per-type contract**: the methods jsongen emitted into `T`'s package meet `J` at `T` and
`*T` (persistent). A theorem of `T`'s package, from its generated code, never an axiom. -/
def typeCodecOk (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (T : go.GoType) : IProp GF :=
  iprop(□ ((∀ x : val, marshalAt J #(methods T go!"JSONModelMarshal" x) (interface.mkOk T x)) ∗
    (∀ l : Loc, marshalAt J #(methods (go.GoType.PointerType T) go!"JSONModelMarshalPtr" #l)
        (interface.mkOk (go.GoType.PointerType T) #l)) ∗
    (∀ l : Loc, unmarshalAt J F #(methods (go.GoType.PointerType T) go!"JSONModelUnmarshal" #l)
        (interface.mkOk (go.GoType.PointerType T) #l))))

instance typeCodecOk_persistent J F T : Persistent (typeCodecOk (GF := GF) J F T) := by
  unfold typeCodecOk; infer_instance

/-- The registered codec's route: a codec of some `fm`, `fu` registered, meeting `J`. -/
def codecRoute (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) :
    IProp GF :=
  iprop(∃ fm fu : GoFunc, codecSetWith fm fu ∗ codecOkWith (jc := J) F fm fu)

/-- **Dispatch of `Marshal(v)`** (`marshalAny`): by `v`'s dynamic type's method set, the method it
calls, else the registered codec. -/
def marshalVia (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (v : GoInterface) : IProp GF :=
  match v with
  | .ok ii =>
    if go.typeSetContains ii.ty encoding.json.modelMarshalerPtr.ty then
      marshalAt J #(methods ii.ty go!"JSONModelMarshalPtr" ii.v) v
    else if go.typeSetContains ii.ty encoding.json.modelMarshaler.ty then
      marshalAt J #(methods ii.ty go!"JSONModelMarshal" ii.v) v
    else codecRoute J F
  | .nil => codecRoute J F

/-- **Dispatch of `Unmarshal(data, ptr)`**: by `ptr`'s dynamic type's method set, its
`JSONModelUnmarshal` (which checks validity with `jsoncodec.Scan`, computing `F`), else the
registered codec. -/
def unmarshalVia (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (ptr : GoInterface) : IProp GF :=
  match ptr with
  | .ok ii =>
    if go.typeSetContains ii.ty encoding.json.modelUnmarshaler.ty then
      iprop(models_lab.jsoncodec.scanOk F models_lab.jsoncodec.scanFn ∗
        unmarshalAt J F #(methods ii.ty go!"JSONModelUnmarshal" ii.v) ptr)
    else codecRoute J F
  | .nil => codecRoute J F

end dispatch

end encoding.json
end Perennial
