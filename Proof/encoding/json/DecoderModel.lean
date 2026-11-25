/-
The model's `*Decoder` (`models/encoding/json/v2_stream.go`, translated with its bodies: `NewDecoder`,
`Decoder.{Decode,readValue,badStart,fetch}`) as a `DecoderRep` (`Registry.lean`), over its fields:

* `decOkModel dec rd I R U`: `dec` points to a `Decoder` reading `rd` whose sticky error is nil; its
  buffer `buf` (its capacity owned) holds the last bytes `bs` of what was read, `R` (`R` ends with
  `bs`), with the stream's resource `I R`; the last value's bounds `prevStart ≤ prevEnd` are within
  `bs`, and `U` is the unread rest, `bs` from `prevEnd` on (`decBufOk`; the capacity below `2^63 / 3`,
  so that `fetch`'s `3*cap(dec.buf)` and `cap(dec.buf)*2` do not overflow);
* `decErrModel dec rd`: `dec` points to a `Decoder` reading `rd` whose sticky error is set, an error
  with a message (`bufio.errOrNil`).

`decRepModel` is that representation. Proved at it: `NewDecoder.spec` (`Codec/NewDecoder.lean`); a
`Decode` over a connection, by its client (vr: `Dsverify`'s `events.Decoder.Decode_frame`, over
`Decoder.fetch_conn.spec`, `Codec/Decoder__fetch_conn.lean`). Definitions only. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.encoding.json.Registry
public import Proof.bufio.ErrOrNil

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- The model `Decoder` `d`'s buffer facts, its buffer holding `bs`: `0 ≤ prevStart ≤ prevEnd ≤
len(bs)`, and its capacity below `2^63 / 3`. -/
def decBufOk [GooseExts] (d : encoding.json.Decoder) (bs : List w8) : Prop :=
  0 ≤ sint.Z d.prevStart' ∧ sint.Z d.prevStart' ≤ sint.Z d.prevEnd' ∧
    sint.Z d.prevEnd' ≤ bs.length ∧ 3 * sint.Z d.buf'.cap < 2 ^ 63

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [encoding.json.Assumptions]

/-- A healthy `*Decoder` (see the file header). -/
def decOkModel (dec : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R U : List w8) :
    IProp GF :=
  iprop(∃ (d : encoding.json.Decoder) (bs pre : List w8), dec ↦ d ∗ d.buf' ↦* bs ∗
    ownSliceCap w8 d.buf' (DFrac.own 1) ∗ I R ∗
    ⌜d.r' = rd ∧ d.err' = interface.nil ∧ R = pre ++ bs ∧ decBufOk d bs ∧
      U = bs.drop (sint.nat d.prevEnd')⌝)

/-- A `*Decoder` whose sticky error is set (see the file header). -/
def decErrModel (dec : Loc) (rd : GoInterface) : IProp GF :=
  iprop(∃ d : encoding.json.Decoder, dec ↦ d ∗ ⌜d.r' = rd ∧ d.err' ≠ interface.nil⌝ ∗
    bufio.errOrNil d.err')

/-- The model's decoder representation (at this heap). -/
@[instance_reducible] def decRepModel : DecoderRep GF :=
  ⟨decOkModel (hG := hG), decErrModel (hG := hG)⟩

theorem decRepModel_decOk (dec : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R U : List w8) :
    (decRepModel (hG := hG)).decOk dec rd I R U = decOkModel (hG := hG) dec rd I R U := rfl

theorem decRepModel_decErr (dec : Loc) (rd : GoInterface) :
    (decRepModel (hG := hG)).decErr dec rd = decErrModel (hG := hG) dec rd := rfl

end defs

end encoding.json
end Perennial
