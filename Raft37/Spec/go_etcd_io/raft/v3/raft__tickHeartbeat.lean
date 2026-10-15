/- Lean-first (no Rocq counterpart).

## `raft.tickHeartbeat` (raft.go), a leader's `r.tick`

`heartbeatElapsed++`, `electionElapsed++`; past the election timeout the counter is reset
(`checkQuorum` and leader transfer are off: `ownRaftPhys`); a leader past the heartbeat
timeout resets that counter and steps a `MsgBeat` from itself: heartbeats to the
followers. Specified like `raft.tickElection`; in any role (a non-leader returns early).
The term does not move.

Lean notes: like `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raft__tickElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.tickHeartbeat.spec : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState),
  NStateWf s →
  -- (2026-10-14, stage B7 part 2) in either ghost mode (`raft.Step.spec`'s)
  (md.isDyn = true → s.role ≠ .preCandidate) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

end spec

end EtcdGrove
end Perennial
