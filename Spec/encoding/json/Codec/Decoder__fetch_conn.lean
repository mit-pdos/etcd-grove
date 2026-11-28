/-
`dec.fetch()` of the encoding/json model's decoder (`models/encoding/json/v2_stream.go`, jsontext's
`decodeBuffer.fetch`) reading the end `s` of a connection `cn` (`net.isConn`, the reader's token
`recvTok` with protocol `P`, read `R`): the bytes kept, `buf[prevStart:]`, move to the front of the
buffer (grown to twice its capacity first, or in place: `copy` within the array), `prevStart` becomes
`0`, `prevEnd` and `baseOffset` move by it, then reads append the next bytes `ys` of the stream to
the buffer until one returns some (`err` nil), or a read fails (`ys` empty): `io.EOF` is returned as
`io.ErrUnexpectedEOF`'s value `ue`, after which the end reads nothing more (`readDead`), and another
error, an `*OpError`, as it is. Called on an end that reads nothing more (`dead`), it returns an
error. The kept bytes are fewer than `2^60` (the caller's: what bounds the buffer's growth, its
capacity staying below `2^63 / 3`, `decBufOk`). Proved in
`Proof/encoding/json/Codec/Decoder__fetch_conn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.DecoderModel
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace encoding.json

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [HasExt netExt] [net.Assumptions] [π : NetProtoGS]

/-- What `fetch` returns (see the file header): `nil` with bytes read (not on a dead end), or no
bytes and `io.ErrUnexpectedEOF`'s value `ue` (the end reading nothing more), or no bytes and an
`*OpError` with a message. -/
def fetchRes (cn : Nat) (s dead : Bool) (ue err : GoInterface) (ys : List w8) : IProp GF :=
  iprop(⌜err = interface.nil ∧ ys ≠ [] ∧ dead = false⌝ ∨
    (⌜ys = [] ∧ err = ue⌝ ∗ readDead (Gg := hG.goose_globalGS) cn s) ∨
    (⌜ys = [] ∧ ∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe⌝ ∗
      bufio.errOrNil err))

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions]
variable [HasExt netExt] [net.Assumptions] [π : NetProtoGS]

/-- See the file header. -/
abbrev Decoder.fetch_conn.spec : Prop :=
  ∀ (dec : Loc) (d : encoding.json.Decoder) (bs : List w8) (cn : Nat) (s : Bool) (a : GoString)
    (P : Proto GF) (R : List w8) (dead : Bool) (ue : GoInterface),
  decBufOk d bs → bs.length - sint.nat d.prevStart' < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ globalAddr io.ErrUnexpectedEOF ↦□ ue ∗
      net.isConn d.r' cn s a ∗ dec ↦ d ∗ d.buf' ↦* bs ∗ ownSliceCap w8 d.buf' (DFrac.own 1) ∗
      recvTok (Gg := hG.goose_globalGS) cn s P R ∗
      (if dead then readDead (Gg := hG.goose_globalGS) cn s else True) }}
    (App (Val (dec @!! go.GoType.PointerType encoding.json.Decoder.ty @!! go!"fetch")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ (d' : encoding.json.Decoder) (ys : List w8),
      dec ↦ d' ∗ d'.buf' ↦* (bs.drop (sint.nat d.prevStart') ++ ys) ∗
      ownSliceCap w8 d'.buf' (DFrac.own 1) ∗ recvTok (Gg := hG.goose_globalGS) cn s P (R ++ ys) ∗
      ⌜d'.r' = d.r' ∧ d'.err' = d.err' ∧ d'.prevStart' = 0 ∧
        d'.prevEnd' = d.prevEnd' - d.prevStart' ∧ d'.baseOffset' = d.baseOffset' + d.prevStart' ∧
        3 * sint.Z d'.buf'.cap < 2 ^ 63⌝ ∗
      fetchRes cn s dead ue err ys }}

end spec

end encoding.json
end Perennial
