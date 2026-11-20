/-
The vocabulary of the specs of the lab's `encoding/json` model (`Proof/encoding/json.lean` for
its package state; notes/vsr-net.md).

**The kit's codec** (`JsonCodec`, a class whose instance a run gives for its generated codec):
* `enc v Ψ`: the deposit for `Marshal(v)` (what the run's `jsonMarshal` needs, e.g. ownership of
  what `v` points to), whose result `Ψ (some bs)` (the encoding `bs`) or `Ψ none` (an error)
  the call returns;
* `dec bs ptr Ψ`: the deposit for `Unmarshal(data, ptr)` of `data`'s bytes `bs` (valid JSON,
  which the model checks first), whose result `Ψ ok` (`ok` iff the error is `nil`) the call
  returns.
`marshalOk`, `unmarshalOk` say the kit's functions meet them (persistent; the run's to prove of
its generated `jsonMarshal`, `jsonUnmarshal`), and `scanOk F` says `jsoncodec.Scan` computes the
Lean function `F` (`Harness/Proof/jsoncodec`). `kitCodecOk F` is all three.

**Validity** (`jsonValid F bs`): `F bs true` is `(0, n)` (Done: a value ends at `n`) and only
JSON whitespace follows: what `Unmarshal` and `Valid` check.
-/
module

public import Harness.Proof.encoding.json
public import Harness.Proof.bufio.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- JSON whitespace (`isSpace` in the model). -/
def isSpaceB (c : w8) : Bool :=
  [W8 32, W8 9, W8 10, W8 13].contains c

/-- `bs` is one JSON value with whitespace around it, by the scanner `F`. -/
def jsonValid (F : List w8 → Bool → w64 × w64) (bs : List w8) : Prop :=
  (F bs true).1 = W64 0 ∧ uint.nat (F bs true).2 ≤ bs.length ∧
    ∀ c ∈ bs.drop (uint.nat (F bs true).2), isSpaceB c = true

instance jsonValid_decidable (F : List w8 → Bool → w64 × w64) (bs : List w8) :
    Decidable (jsonValid F bs) := by
  unfold jsonValid; infer_instance

/-- The kit's codec, as the specs see it (see the file header). -/
class JsonCodec [GooseExts] (GF : BundledGFunctors) where
  enc : GoInterface → (Option (List w8) → IProp GF) → IProp GF
  dec : List w8 → GoInterface → (Bool → IProp GF) → IProp GF

section defs
variable [JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [JsonCodec GF]

/-- `Marshal`'s function meets `JsonCodec.enc`: the encoding in a fresh slice (with its capacity)
and no error, or an error (any slice). -/
def marshalOk (fm : GoFunc) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : Option (List w8) → IProp GF) (Φ : val → IProp GF),
    JsonCodec.enc v Ψ -∗
    ▷ ((∀ (s : GoSlice) (bs : List w8), s ↦* bs -∗ ownSliceCap w8 s (DFrac.own 1) -∗
          Ψ (some bs) -∗
          Φ (PairV #s #(interface.nil : GoInterface))) ∧
       (∀ (s : GoSlice) (err : GoInterface), ⌜err ≠ interface.nil⌝ -∗ Ψ none -∗
          Φ (PairV #s #err))) -∗
    WP (App (Val #fm) (Val #v)) {{ Φ }})

/-- `Unmarshal`'s function meets `JsonCodec.dec`, on valid JSON. -/
def unmarshalOk (F : List w8 → Bool → w64 × w64) (fu : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    ⌜jsonValid F bs⌝ -∗ data ↦*{dq} bs -∗ JsonCodec.dec bs ptr Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗
        ⌜err = interface.nil ↔ ok = true⌝ -∗ Ψ ok -∗ Φ #err) -∗
    WP (App (App (Val #fu) (Val #data)) (Val #ptr)) {{ Φ }})

/-- `Scan`'s function computes `F` (reading its slice); `F`'s end is within the input. -/
def scanOk (F : List w8 → Bool → w64 × w64) (fs : GoFunc) : IProp GF :=
  iprop(⌜∀ bs eof, uint.nat (F bs eof).2 ≤ bs.length⌝ ∗ □ ∀ (s : GoSlice) (dq : DFrac) (bs : List w8) (eof : Bool) (Φ : val → IProp GF),
    s ↦*{dq} bs -∗ ▷ (s ↦*{dq} bs -∗ Φ (PairV #(F bs eof).1 #(F bs eof).2)) -∗
    WP (App (App (Val #fs) (Val #s)) (Val #eof)) {{ Φ }})

instance marshalOk_persistent (fm : GoFunc) : Persistent (marshalOk (GF := GF) fm) := by
  unfold marshalOk; infer_instance
instance unmarshalOk_persistent F (fu : GoFunc) : Persistent (unmarshalOk (GF := GF) F fu) := by
  unfold unmarshalOk; infer_instance
instance scanOk_persistent F (fs : GoFunc) : Persistent (scanOk (GF := GF) F fs) := by
  unfold scanOk; infer_instance

/-- The kit's codec functions meet `JsonCodec`, and `jsoncodec.Scan` computes `F` (persistent). -/
def kitCodecOk (F : List w8 → Bool → w64 × w64) : IProp GF :=
  iprop(marshalOk (kitFn go!"jsonMarshal") ∗ unmarshalOk F (kitFn go!"jsonUnmarshal") ∗
    scanOk F scanFn)

instance kitCodecOk_persistent F : Persistent (kitCodecOk (GF := GF) F) := by
  unfold kitCodecOk; infer_instance

/-- A codec with the kit's functions is registered, for good (persistent). -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.json.codec ↦□ c ∗ codecFns c)

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

end defs

end encoding.json

end Perennial
