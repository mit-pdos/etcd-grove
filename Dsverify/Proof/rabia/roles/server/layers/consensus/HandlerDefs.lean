/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/HandlerDefs.lean`, run `rabia-r1wake-1`.)

The message handler's state between messages and its witnesses of the processed messages.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Basics
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Pure

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- The frozen rounds' authority, with a copy of each element. -/
def frzRes (γc : ConsNames) : IProp GF :=
  iprop(∃ F : GMap (Nat × Nat) Unit, ghostMapAuth γc.frz 1 F ∗
    [∗map] k ↦ _u ∈ F, roundDone γc k.1 k.2)

/-- The handler's part of slot `s` between messages (no pending notification). -/
def hSlot (γl : SrvNames) (γc : ConsNames) (s : Nat) : IProp GF :=
  iprop(∃ (sent : List Msg) (ents : List Ent) (ql : List (Option Nat)),
    spscProducer (γc.queue s) sent ∗ ⌜sent.length = ql.length⌝ ∗
    monoListAuthOwn (γc.qlog s) (1 : Qp).half ql ∗
    monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ∗
    ghostVar (pendName γl γc s) (1 : Qp).half (none : Option (Option Nat)))

/-- Sender `X`'s message of round `ρ` at slot `s` was processed: counted, or the round notified, or
the slot done. -/
def doneOr (γl : SrvNames) (γc : ConsNames) (s ρ X : Nat) : IProp GF :=
  iprop(counted γl γc s ρ X ∨ notified γc s ρ ∨ doneW γl γc s)

/-- What processing message `m` of sender `X` leaves (persistent). -/
def msgWit (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) : IProp GF :=
  match msgRound m with
  | some (s, ρ) => if s < lenLedger then doneOr γl γc s ρ X else iprop(True)
  | none => iprop(True)

/-- What processing message `m` of sender `X` needs: its sender's message of the round before. -/
def prevWit (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) : IProp GF :=
  match msgRound m with
  | some (s, ρ + 1) => if s < lenLedger then doneOr γl γc s ρ X else iprop(True)
  | _ => iprop(True)

/-- The witness of a processed `B_X[j]`. -/
def procWit (γ : Names) (γl : SrvNames) (γc : ConsNames) (x : Nat × Nat) : IProp GF :=
  iprop(∃ (l : List MsgV) (m : MsgV), bcastLb γ x.1 l ∗ ⌜l[x.2]? = some m⌝ ∗ msgWit γl γc x.1 m)

instance doneOr_persistent (γl : SrvNames) (γc : ConsNames) (s ρ X : Nat) :
    Persistent (doneOr (GF := GF) γl γc s ρ X) := by
  unfold doneOr counted notified doneW qLb; infer_instance
instance msgWit_persistent (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) :
    Persistent (msgWit (GF := GF) γl γc X m) := by
  unfold msgWit; split
  · split <;> infer_instance
  · infer_instance
instance prevWit_persistent (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) :
    Persistent (prevWit (GF := GF) γl γc X m) := by
  unfold prevWit; split
  · split <;> infer_instance
  · infer_instance
instance procWit_persistent (γ : Names) (γl : SrvNames) (γc : ConsNames) (x : Nat × Nat) :
    Persistent (procWit (GF := GF) γ γl γc x) := by
  unfold procWit bcastLb; infer_instance

end defs

end Perennial.rabia.roles.server.layers.consensus
