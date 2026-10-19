/-
`(*raft).getWitnessVoteRequestReadiness` (raft#168, `raft.go`; 2026-10-19, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `r.getWitnessVoteRequestReadiness(votesToWin)` on a witness-free configuration
(`ownRaftPhysC`'s tracker, `Witnesses = [0, 0]`): no witness to ask, `nil` (with both halves
past one vote to win the first `return nil`, else the second). `stepCandidate`'s
`VotePending` arm then ranges over nothing. -/
abbrev raft.getWitnessVoteRequestReadiness.spec : Prop :=
  ∀ (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState) (d : GoArray w64 2),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"getWitnessVoteRequestReadiness"))
      (Val #d))
  {{ RET #map.nil; ownRaftPhysCV c V r id s }}

end spec

end EtcdGrove
end Perennial
