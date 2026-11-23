/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Internal.lean`, run `rabia-r1wake-1`.)

`rabia/internal/message`'s internal specs (prover C1; used by C2's framing proofs).

* `ConsensusObj.Unmarshal`, `Msg.Unmarshal`, `Command.Unmarshal`: decoding an encoding
  (`encObj`/`encMsg`/`encCmd`, `Proof/Rabia/Model.lean`) into a zero value gives a value holding
  the record. No well-formedness premise: every record round-trips (a negative `Msg.Type` is
  encoded as a 10-byte varint, decoded back by `int32` shifts that drop the high bits).
* `Msg.Marshal.boundedSpec`, `Command.Marshal.boundedSpec`: the frozen `Marshal` specs under a
  bound on the encoding's length (`< 2 ^ 32`, as `MarshalWriteFlush`'s premise): without one, the
  generated `Size` (an `int` sum) and `MarshalToSizedBuffer`'s packed buffer
  (`make([]byte, len(m.CliSeqs)*10)`) overflow for (unrealistically) huge messages
  (notes/hub-requests.md). Superseded: H-C1-1 was accepted (the frozen specs carry the bound);
  these two statements are not proved (generic in the package instance they lack `isPkgInit
  math/bits`); use `Command.Marshal.wp_proof` (Marshal.lean) / the frozen specs.
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

/-- `(*ConsensusObj).Unmarshal(dAtA)` of an encoding, into a zero `ConsensusObj`. -/
abbrev ConsensusObj.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (sl : GoSlice) (dq : DFrac) (o : ObjV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
      l ↦ (zeroValDef : ConsensusObj) ∗ sl ↦*{dq} encObj o }}
    (App (Val (l @!! go.GoType.PointerType ConsensusObj.ty @!! go!"Unmarshal")) (Val #sl))
  {{ RET #interface.nil; ∃ v, l ↦ v ∗ objRep v o ∗ sl ↦*{dq} encObj o }}

/-- `(*Msg).Unmarshal(dAtA)` of an encoding, into a zero `Msg`. -/
abbrev Msg.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (sl : GoSlice) (dq : DFrac) (m : MsgV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
      l ↦ (zeroValDef : Msg) ∗ sl ↦*{dq} encMsg m }}
    (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"Unmarshal")) (Val #sl))
  {{ RET #interface.nil; ∃ v, l ↦ v ∗ msgRep v m ∗ sl ↦*{dq} encMsg m }}

/-- `(*Command).Unmarshal(dAtA)` of an encoding, into a zero `Command`. -/
abbrev Command.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (sl : GoSlice) (dq : DFrac) (c : CmdV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
      l ↦ (zeroValDef : Command) ∗ sl ↦*{dq} encCmd c }}
    (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"Unmarshal")) (Val #sl))
  {{ RET #interface.nil; ∃ v, l ↦ v ∗ cmdRep v c ∗ sl ↦*{dq} encCmd c }}

/-- `(*Msg).Marshal()` of a message whose encoding is shorter than `2 ^ 32`. -/
abbrev Msg.Marshal.boundedSpec : Prop :=
  ∀ (l : Loc) (v : Msg) (m : MsgV) (dq : DFrac),
  (encMsg m).length < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦{dq} v ∗ msgRep v m }}
    (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encMsg m }}

/-- `(*Command).Marshal()` of a command whose encoding is shorter than `2 ^ 32`. -/
abbrev Command.Marshal.boundedSpec : Prop :=
  ∀ (l : Loc) (v : Command) (c : CmdV) (dq : DFrac),
  (encCmd c).length < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦{dq} v ∗ cmdRep v c }}
    (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encCmd c }}

end spec

end Perennial.rabia.internal.message
