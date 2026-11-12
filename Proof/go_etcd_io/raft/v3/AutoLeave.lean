/-
The automatic leave of a joint configuration (2026-10-29, stage U5): the proposal `raft.appliedTo`
steps (`confChangeToMsg(nil)`), the step it takes (`LeaveStep`, `raft.appliedTo.spec`'s post), and
that its entry decodes (`ccEntsOk_leave`, from the trust-base fact `ccDecodeV2_nil`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- **The automatic leave's proposal** (2026-10-29, stage U5): what `appliedTo` steps,
`confChangeToMsg(nil)` (`raftpb/confchange.go:40-45`): a local `MsgProp` (`Term = 0`, `From = 0`)
whose one entry is an empty `EntryConfChangeV2`. -/
def leaveMsgM : MessageM := { (zero_val MessageM) with Type' := MsgProp }

/-- The leave's entry: type `EntryConfChangeV2` (`2`), no data, not yet stamped. -/
def leaveEntM : EntryM := ⟨W64 0, W64 0, W32 2, []⟩

/-- The leave's proposal as the protocol sees it. -/
def leaveAbs : Msg := absMsg .propose leaveMsgM [leaveEntM] []

/-- **What `appliedTo` did after moving `applied`** (2026-10-29, stage U5), from `s1` (the state at
the new `applied`) to `s'`: nothing (`recv = []`, the bound `B` the log's last index), or -- a leader
at a configuration it leaves automatically -- `r.Step` of its leave's proposal (`leaveMsgM`), the
step `wp_Step_MsgProp` gives: the proposal received (`recv`) when appended, one `StepCD` step at the
bound `B` the appended entry is at, keeping the frame `RawNode` relies on (`LocalFrame`, `applying`,
`applied`) and the role; with the room in the log a dropped proposal's indices need (`DynHyp`). -/
def LeaveStep (c : CfgM) (id : w64) (s1 s' : NState) (B : Int) (recv : List Msg) : Prop :=
  (s' = s1 ∧ recv = [] ∧ B = plogLastIndexZ (toPState s1).base (toPState s1).log) ∨
  (c.autoLeave = true ∧ s1.role = .leader ∧
    (∀ m' ∈ recv, m' = leaveAbs) ∧ recv.length ≤ 1 ∧
    StepCD c id B leaveMsgM s1 recv s' ∧
    LocalFrame s1 s' ∧ s'.logst.applying = s1.logst.applying ∧
    s'.logst.applied = s1.logst.applied ∧ NStateWf s' ∧
    plogLastIndexZ (toPState s1).base (toPState s1).log ≤ B ∧
    B ≤ plogLastIndexZ (toPState s1).base (toPState s1).log + 1 ∧ B < 2 ^ 64 ∧
    plogLastIndexZ (toPState s1).base (toPState s1).log + 2 ^ 61 < 2 ^ 64)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The leave's entry decodes: `stepLeader` `Unmarshal`s its empty data into the empty
`ConfChangeV2` (`ccDecodeV2_nil`, the trust-base fact). -/
theorem ccEntsOk_leave :
    ⊢ ccEntsOk (GF := GF) [leaveEntM] [some (.v2 ConfChangeV2M.empty)] := by
  unfold ccEntsOk
  iapply (BigSepL2.bigSepL2_cons (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  isplitl
  · simp only [ccEntOk]
    ipureintro; exact ⟨rfl, ccDecodeV2_nil⟩
  iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => ccEntOk (GF := GF) e o)).2
  iempintro

end lemmas

end EtcdGrove
end Perennial
