/-
`enc.Encode(v)` over the encoding/json model's registered codec, on an encoder writing to a
connection end (mit-pdos/etcd-grove#24, item 1). Moved from `Dsverify`'s vr kit
(`encoding.json.Encoder.Encode_conn.spec`, the lab's `jsonstream.wp_Encode_conn`), with the
registry generic in the codec's functions `fm`, `fu` (`Unmarshal`'s header). Stated over the
connection (`net.isConn`, `sendTok`) rather than a generic writer contract: the model's `Encode`
writes the encoding and a newline in one `Write` (Go's), and a connection's `Write` error has no
`Error` spec in `Net/` for a generic `errOrNil` writer contract. `net`'s initialization: a write error may be
`internal/poll.ErrDeadlineExceeded`'s value (`net.Conn.Write.spec`). Proved at the model's encoder,
`Proof/encoding/json/Codec/Encoder__Encode_conn.lean`. (#24 J2/J3, 2026-11-23: `marshalVia J F v`, the contract `J` explicit, in place of
`codecSetWith fm fu ∗ codecOkWith F fm fu`, its codec case.) Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry
public import Proof.bufio.ErrOrNil
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [EncoderRep GF]
variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- `enc.Encode(v)` (`net` initialized), `enc` a healthy encoder writing to the end `s` of a connection `cn`
(`net.isConn`) whose written stream (protocol `P`) is `W`, the encoding allowed after `W`, `v`
marshalled by its own method or the registered codec (`marshalVia J F v`, #24 J3), meeting `J`: `Marshal` failed (`err` non-nil, `Ψ none`,
nothing written); or the encoding `bs` and a newline were written in one `Write`, `k` bytes of them
(all of them when `err` is nil), `err` some error or nil. -/
abbrev Encoder.Encode_conn.spec : Prop :=
  ∀ (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) (enc : Loc) (v w : GoInterface) (cn : Nat)
    (s : Bool) (a : GoString) (P : Proto GF) (W : List w8) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ isPkgInit (PROP := IProp GF) pkg_id.net ∗
      marshalVia J F v ∗
      EncoderRep.encOk (GF := GF) enc w ∗
      net.isConn w cn s a ∗ sendTok cn s P W ∗ J.enc v Ψ ∗
      (∀ bs, Ψ (some bs) -∗ □ P cn (W ++ (bs ++ [W8 10])) ∗ Ψ (some bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.json.Encoder.ty @!! go!"Encode")) (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ interface.nil⌝ ∗ sendTok cn s P W ∗ Ψ none) ∨
      (∃ (bs : List w8) (k : Nat),
        ⌜k ≤ bs.length + 1 ∧ (err = interface.nil → k = bs.length + 1)⌝ ∗
        sendTok cn s P (W ++ (bs ++ [W8 10]).take k) ∗ Ψ (some bs) ∗
        bufio.errOrNil err) }}

end spec

end encoding.json
end Perennial
