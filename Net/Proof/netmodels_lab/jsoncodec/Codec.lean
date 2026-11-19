/-
What a generated JSON codec (`etc/jsongen.py`: `jsonMarshal`, `jsonUnmarshal`, over `jsoncodec`)
is proved to meet, per program: the obligations a model of `encoding/json` takes of the codec
registered with it (phase 5 of notes/dsverify-net-port-plan.md). Ported from dsverify-lab's
`Harness/Proof/encoding/json/Defs.lean` (`348a866`; its parts about the generated codec, not about
the model's registry), the statements kept; what changed is in the plan note, phase 5 item 1.

**The codec** (`JsonCodec`, a class whose instance the program's proof gives for its codec):
* `enc v Ψ`: the deposit for `Marshal(v)` (what the program's `jsonMarshal` needs, e.g. ownership
  of what `v` points to), whose result `Ψ (some bs)` (the encoding `bs`) or `Ψ none` (an error)
  the call returns;
* `dec bs ptr Ψ`: the deposit for `Unmarshal(data, ptr)` of `data`'s bytes `bs` (valid JSON,
  which the model checks first), whose result `Ψ ok` (`ok` iff the error is `nil`) the call
  returns.
`marshalOk`, `unmarshalOk` say the program's functions meet them (persistent; its proof proves them
of its generated `jsonMarshal`, `jsonUnmarshal`), and `scanOk F` says `jsoncodec.Scan` (`scanFn`)
computes the Lean function `F`.

**Validity** (`jsonValid F bs`): `F bs true` is `(0, n)` (Done: a value ends at `n`) and only
JSON whitespace (`spaceB`) follows: what `Unmarshal` and `Valid` check.
-/
module

public import Net.Proof.netmodels_lab.Errors
public import Net.Proof.netmodels_lab.jsoncodec.Base
public import Net.Spec.netmodels_lab.jsoncodec.Error__Error

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace netmodels_lab.jsoncodec

/-- `bs` is one JSON value with whitespace around it, by the scanner `F`. -/
def jsonValid (F : List w8 → Bool → w64 × w64) (bs : List w8) : Prop :=
  (F bs true).1 = W64 0 ∧ uint.nat (F bs true).2 ≤ bs.length ∧
    ∀ c ∈ bs.drop (uint.nat (F bs true).2), spaceB c = true

instance jsonValid_decidable (F : List w8 → Bool → w64 × w64) (bs : List w8) :
    Decidable (jsonValid F bs) := by
  unfold jsonValid; infer_instance

/-- The program's JSON codec, as the specs see it (see the file header). -/
class JsonCodec [GooseExts] (GF : BundledGFunctors) where
  enc : GoInterface → (Option (List w8) → IProp GF) → IProp GF
  dec : List w8 → GoInterface → (Bool → IProp GF) → IProp GF

/-- `jsoncodec.Scan`, the scanner every codec registers. -/
def scanFn [GooseExts] [GoSemanticsFunctions] : GoFunc :=
  functions go!"netmodels.lab/jsoncodec.Scan" []

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [JsonCodec GF]

/-- `Marshal`'s function `fm` meets `JsonCodec.enc`: the encoding in a fresh slice (with its
capacity) and no error, or an error (any slice). -/
def marshalOk (fm : GoFunc) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : Option (List w8) → IProp GF) (Φ : val → IProp GF),
    JsonCodec.enc v Ψ -∗
    ▷ ((∀ (s : GoSlice) (bs : List w8), s ↦* bs -∗ ownSliceCap w8 s (DFrac.own 1) -∗
          Ψ (some bs) -∗
          Φ (PairV #s #(interface.nil : GoInterface))) ∧
       (∀ (s : GoSlice) (err : GoInterface), ⌜err ≠ interface.nil⌝ -∗ Ψ none -∗
          Φ (PairV #s #err))) -∗
    WP (App (Val #fm) (Val #v)) {{ Φ }})

/-- `Unmarshal`'s function `fu` meets `JsonCodec.dec`, on valid JSON. -/
def unmarshalOk (F : List w8 → Bool → w64 × w64) (fu : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    ⌜jsonValid F bs⌝ -∗ data ↦*{dq} bs -∗ JsonCodec.dec bs ptr Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗
        ⌜err = interface.nil ↔ ok = true⌝ -∗ Ψ ok -∗ Φ #err) -∗
    WP (App (App (Val #fu) (Val #data)) (Val #ptr)) {{ Φ }})

/-- `Scan`'s function `fs` computes `F` (reading its slice); `F`'s end is within the input. -/
def scanOk (F : List w8 → Bool → w64 × w64) (fs : GoFunc) : IProp GF :=
  iprop(⌜∀ bs eof, uint.nat (F bs eof).2 ≤ bs.length⌝ ∗ □ ∀ (s : GoSlice) (dq : DFrac)
      (bs : List w8) (eof : Bool) (Φ : val → IProp GF),
    s ↦*{dq} bs -∗ ▷ (s ↦*{dq} bs -∗ Φ (PairV #(F bs eof).1 #(F bs eof).2)) -∗
    WP (App (App (Val #fs) (Val #s)) (Val #eof)) {{ Φ }})

instance marshalOk_persistent (fm : GoFunc) : Persistent (marshalOk (GF := GF) fm) := by
  unfold marshalOk; infer_instance
instance unmarshalOk_persistent F (fu : GoFunc) : Persistent (unmarshalOk (GF := GF) F fu) := by
  unfold unmarshalOk; infer_instance
instance scanOk_persistent F (fs : GoFunc) : Persistent (scanOk (GF := GF) F fs) := by
  unfold scanOk; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : netmodels_lab.jsoncodec.Assumptions]

/-- `*jsoncodec.Error` is in the type set of `error` (its method `Error() string`). -/
theorem Error_is_error :
    go.typeSetContains (go.GoType.PointerType Error.ty) go.error = true := by
  go_type_set

/-- A `*jsoncodec.Error` kept for good (`↦□`) is some error. -/
theorem Error_errAny (wp_Error : Error.Error.spec (GF := GF) (hG := hG)) (e : Loc) (v : Error) :
    (e ↦□ v : IProp GF) ⊢ errAny (interface.mkOk (go.GoType.PointerType Error.ty) #e) := by
  iintro #He
  unfold errAny
  iexists (interface.mk (go.GoType.PointerType Error.ty) #e)
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Error_is_error
  imodintro
  iintro %Φ Hk
  wp_apply (wp_Error e v)
  · iexact He
  iapply Hk

end laws

end netmodels_lab.jsoncodec
end Perennial
