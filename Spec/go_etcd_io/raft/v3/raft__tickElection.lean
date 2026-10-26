/- Lean-first (no Rocq counterpart).

## `raft.tickElection` (raft.go), a non-leader's `r.tick`

`electionElapsed++`; once past the (randomized) election timeout, a node that can be
leader (`promotable`) resets the counter and steps a `MsgHup` from itself: it campaigns.
Specified like `raft.Step` (the ghost state in either mode, since 2026-10-14 `ownStepGhost`), with what `RawNode.Tick` needs
of the physical state: `TickStep`. In any role: a leader's `MsgHup` is ignored.

Lean notes: like `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- What a tick does to the physical state beyond the protocol: the log as `NetFrame`
keeps it, the term up by at most one (a campaign), `offsetInProgress` not back. -/
def TickStep [GooseExts] (s s' : NState) : Prop :=
  NetFrame s s' ∧ uint.Z s.term ≤ uint.Z s'.term ∧ uint.Z s'.term ≤ uint.Z s.term + 1 ∧
  uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress ∧
  -- (2026-10-17) a pre-candidate afterwards is at the term before (a pre-campaign keeps it)
  (s'.role = .preCandidate → s'.term = s.term) ∧
  -- (2026-10-25, T-M M2b) and its campaign guard kept (`PreGuardF.step`)
  (∀ fp : List EntryM, PreGuardF fp s → PreGuardF fp s')

theorem TickStep.refl [GooseExts] (s : NState) : TickStep s s :=
  ⟨NetFrame.refl s, Int.le_refl _, by omega, Int.le_refl _, fun _ => rfl, fun _ h => h⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.tickElection.spec : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  -- a campaign increments the term; `send` panics if it wraps
  uint.Z s.term + 1 < 2 ^ 64 →
  -- (2026-10-17) a pre-campaign's next term within the ceiling (`NGhost.tc`)
  (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  NStateWf s →
  -- (D19i part 1) the floor at most `applied` (a campaign's `hup`)
  uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  -- (2026-10-14, stage B7 part 2) in either ghost mode (`raft.Step.spec`'s); in the dynamic one
  -- a pre-candidate's campaign guard (`GMode.Guard`; until 2026-10-25 no pre-candidate)
  md.Guard s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickElection")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

end spec

end EtcdGrove
end Perennial
