/- Lean-first (no Rocq counterpart). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.softState()`: `SoftState{Lead: r.lead, RaftState: r.state}`. -/
abbrev raft.softState.spec : Prop :=
  -- (2026-10-14, stage B7 part 2) at any configuration (until then `ownRaftPhys cfg`)
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ ownRaftPhysCV (GF := GF) c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"softState")) (Val #()))
  {{ RET #(softstateVal (nodeSoftstate s)); ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
