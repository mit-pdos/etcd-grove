/- Lean-first (no Rocq counterpart). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `electionElapsed >= randomizedElectionTimeout`, two fields the abstraction does not
track: some `bool`, the state unchanged. -/
abbrev raft.pastElectionTimeout.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  -- (2026-10-14, stage B7 part 2) at any configuration (until then `ownRaftPhys cfg`)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"pastElectionTimeout")) (Val #()))
  {{ (b : Bool), RET #b; ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
