/- Lean-first (no Rocq counterpart).

## `raft.tickHeartbeat` (raft.go), a leader's `r.tick`

`heartbeatElapsed++`, `electionElapsed++`; past the election timeout the counter is reset,
(2026-10-17) with `checkQuorum` on a `MsgCheckQuorum` is stepped (a leader may step down at its
term), and a leader's transfer in progress is aborted; a leader past the heartbeat
timeout resets that counter and steps a `MsgBeat` from itself: heartbeats to the
followers. Specified like `raft.tickElection`; in any role (a non-leader returns early).
The term does not move.

Lean notes: like `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__tickElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. (2026-11-10, Q8 stage 1 slice 12 of `notes/trace-validation-plan.md`) **One spec
for both modes**, in place of stage 0's premise `s.gh.tr = none`. A tick may step twice, each `Step`
taking the caller's resources through `raft.Step.spec`'s gates and closing wand:
- the quorum check (`checkQuorum` on, past the election timeout: `tickMsg MsgCheckQuorum id`) at `s`,
  from `R.G`, ending in the caller's `Gm` at its end state; with no quorum check the caller turns
  `R.G` into `Gm s` (`"Hskip"`);
- the heartbeat (a leader past the heartbeat timeout: `tickMsg MsgBeat id`), at the state `s2` the
  first part left: `s1` (`s` or the quorum check's end state, of which the caller holds `Gm s1`), its
  leader transfer aborted or not (`abortLeaderTransfer`, untraced); the caller gives that step's
  resources, gates and closing wand from `Gm s1` (`"Hgbeat"`), ending in its `Gout`.
The caller gets back `Gm s1` (no heartbeat) or `Gout` at the end state. The untraced instance is
`raft.tickHeartbeat.untraced` (`TracedUntracedTick.lean`), the statement before slice 12, which
`RawNode.Tick` uses. -/
abbrev raft.tickHeartbeat.spec : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    (R : StepG GF) (Gm Gout : NState → IProp GF),
  NStateWf s →
  -- (2026-10-14, stage B7 part 2) in either ghost mode (`raft.Step.spec`'s)
  -- (2026-10-25, T-M M2b) a pre-candidate's campaign guard (until then no pre-candidate)
  md.Guard s →
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`, until 2026-11-10, slice 12: the
  -- premise `s.gh.tr = none`) each `Step` takes the caller's resources through its gates
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      "HG" ∷ R.G ∗
      -- the quorum check's `Step`, at `s`
      "Hgcq" ∷ (⌜s.cq = true⌝ -∗
        stepGates c r id s (tickMsg MsgCheckQuorum id) [] none [] [] (ghostIn γ md c id s R) ∗
        stepClose γ md c id (tickMsg MsgCheckQuorum id) [] [] s R Gm) ∗
      -- no quorum check
      "Hskip" ∷ (R.G ={⊤}=∗ Gm s) ∗
      -- the heartbeat's `Step`, at the state the first part left
      "Hgbeat" ∷ (∀ (s1 s2 : NState), ⌜s2.gh = s.gh ∧ s2.role = .leader ∧
          (s2 = s1 ∨ s2 = { s1 with lt := W64 0 })⌝ -∗ Gm s1 ={⊤}=∗
        ∃ R2 : StepG GF, R2.G ∗
          stepGates c r id s2 (tickMsg MsgBeat id) [] none [] [] (ghostIn γ md c id s2 R2) ∗
          stepClose γ md c id (tickMsg MsgBeat id) [] [] s2 R2 Gout) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      -- (2026-11-01, durability stage II (m)) and the term and the vote as the model moves them
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
        PVoteLe (toPState s) (toPState s')⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ ∗
      -- (slice 12) no heartbeat: the first part's resource; else the heartbeat `Step`'s
      "HG" ∷ ((∃ s1 : NState, ⌜s' = s1 ∨ s' = { s1 with lt := W64 0 }⌝ ∗ Gm s1) ∨ Gout s') }}

end spec

end EtcdGrove
end Perennial
