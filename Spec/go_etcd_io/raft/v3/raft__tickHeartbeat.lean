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

public import Spec.go_etcd_io.raft.v3.raft__tickElection

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
  ∀ (cfg : GSet w64) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ps : PState),
  γ.reCfg = cfg →
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hghost" ∷ ownRaftGhost γ id ps }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState) (ps' : PState), RET #();
      "Hphys" ∷ ownRaftPhys cfg r id s' ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ }}

end spec

end EtcdGrove
end Perennial
