/- Lean-first (no Rocq counterpart, 2026-10-13). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__hardState
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__softState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts]

/-- The `BasicStatus` of a node `id` in physical state `s`: its id, `r.hardState()`,
`r.softState()`, `r.raftLog.applied` and `r.leadTransferee` (`NState.lt`).

raft v3.7 (2026-10-15, stage R4): `BasicStatus` embeds a `*pb.HardState`, the pointer `hp`
`r.hardState()` returns (`hsRO hp (hardstateVal (nodeHardstate s))` in the spec's post). -/
def basicStatusOf (id : w64) (s : NState) (hp : Loc) : BasicStatus :=
  BasicStatus.mk id hp (softstateVal (nodeSoftstate s))
    s.logst.applied s.lt

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `getBasicStatus(r)` (status.go:56): reads only; returns `basicStatusOf id s`. -/
abbrev getBasicStatus.spec : Prop :=
  -- (2026-10-14, stage B7 part 2) at any configuration (until then `ownRaftPhys cfg`)
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ ownRaftPhysCV (GF := GF) c c.voters r id s }}
    (App (Val #(functions getBasicStatus [])) (Val #r))
  {{ (hp : Loc), RET #(basicStatusOf id s hp);
      hsRO hp (hardstateVal (nodeHardstate s)) ∗ ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
