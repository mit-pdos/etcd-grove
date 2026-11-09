/-
Lean-first (no Rocq counterpart). `raft.campaign`'s role transition and its facts, moved out of the
proof file (`raft__campaign.lean`) on 2026-11-09 (trace-check Q8 stage 1 slice 5), so that the proof
file exposes only its `wp_proof` (CLAUDE.md, "Package APIs": `campRoleState_gh`, added by Q8 stage 0,
was a layout violation, `etc/gen-interface.py --layout`).
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section helpers
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The role transition `campaign` makes, by `pre`. -/
def campRoleState (id : w64) (s : NState) (pre : Bool) : NState :=
  if pre then becomePrecandidate s else becomeCandidate id s

/-- (Q8 stage 0) The campaign's role change keeps the ghost (the trace mode). -/
theorem campRoleState_gh (id : w64) (s : NState) (pre : Bool) :
    (campRoleState id s pre).gh = s.gh := by
  cases pre <;> rfl

theorem campRoleState_logst (id : w64) (s : NState) (pre : Bool) :
    (campRoleState id s pre).logst = s.logst := by
  cases pre <;> rfl

end helpers

end EtcdGrove
end Perennial
