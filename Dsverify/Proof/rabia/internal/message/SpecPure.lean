/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Spec.lean`, run
`rabia-r1wake-1`: its specs that do not involve `bufio`; those that do (`BufWrite`, `WriteFlush`,
`*.MarshalWriteFlush`, `BufRead`, `*.ReadUnmarshal`) wait for the shared bufio change.)

`rabia/internal/message`'s specs used by other packages, without `bufio`:
* `Msg.Marshal`, `Command.Marshal`: a fresh slice holding the encoding (gogo-protobuf's).
* `ProxySeqIdEqual`, `ProxySeqIdLessThan`: pure.
-/
module

public import Dsverify.Proof.rabia.internal.message.Rep
public import Dsverify.Proof.rabia.internal.message.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

/-- `(*Msg).Marshal()`: a fresh slice holding `encMsg m`, no error. -/
abbrev Msg.Marshal.spec : Prop :=
  ∀ (l : Loc) (v : Msg) (m : MsgV) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦{dq} v ∗ msgRep v m ∗
      ⌜(encMsg m).length < 2 ^ 32⌝ }}
    (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encMsg m }}

/-- `(*Command).Marshal()`. -/
abbrev Command.Marshal.spec : Prop :=
  ∀ (l : Loc) (v : Command) (c : CmdV) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦{dq} v ∗ cmdRep v c ∗
      ⌜(encCmd c).length < 2 ^ 33⌝ }}
    (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encCmd c }}

/-- `ProxySeqIdEqual(c1, c2)`: the ids are equal. -/
abbrev ProxySeqIdEqual.spec : Prop :=
  ∀ (l1 l2 : Loc) (v1 v2 : ConsensusObj) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}
    (App (App (Val (@! ProxySeqIdEqual)) (Val #l1)) (Val #l2))
  {{ RET #(decide (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId' = v2.ProId'));
      l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}

/-- `ProxySeqIdLessThan(c1, c2)`: the ids' order. -/
abbrev ProxySeqIdLessThan.spec : Prop :=
  ∀ (l1 l2 : Loc) (v1 v2 : ConsensusObj) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}
    (App (App (Val (@! ProxySeqIdLessThan)) (Val #l1)) (Val #l2))
  {{ RET #(decide (v1.ProSeq'.toNat < v2.ProSeq'.toNat ∨
        (v1.ProSeq' = v2.ProSeq' ∧ v1.ProId'.toNat < v2.ProId'.toNat)));
      l1 ↦{dq1} v1 ∗ l2 ↦{dq2} v2 }}

end spec

end Perennial.rabia.internal.message
