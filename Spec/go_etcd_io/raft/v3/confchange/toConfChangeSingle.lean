/-
## `toConfChangeSingle(cs)` (internal)

**Users.** `Restore`. Mirrors the code: fresh `ConfChangeSingle`s, the outgoing voters' adds, and
the incoming changes (remove the outgoing voters, add the voters, the learners and the staged
learners as learners), as `ConfChange.restore` lists them.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api
public import Spec.go_etcd_io.raft.v3.raftpb.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) The ops `Restore` runs for `ConfState` `csv`. -/
def toConfChangeSingle.spec : Prop :=
  ∀ (csp : Loc) (dq : DFrac) (csv : RaftPb.ConfState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ RaftPb.confStatePts csp dq csv }}
    (App (Val #(functions go_etcd_io.raft.v3.confchange.toConfChangeSingle [])) (Val #csp))
  {{ (out inc : GoSlice), RET (PairV #out #inc); RaftPb.confStatePts csp dq csv ∗
      ccsPts out (DFrac.own 1) (csv.votersOutgoing.map (fun id => ⟨AddNode, id⟩)) ∗
      ccsPts inc (DFrac.own 1)
        (csv.votersOutgoing.map (fun id => ⟨RemoveNode, id⟩) ++
         csv.voters.map (fun id => ⟨AddNode, id⟩) ++
         csv.learners.map (fun id => ⟨AddLearnerNode, id⟩) ++
         csv.learnersNext.map (fun id => ⟨AddLearnerNode, id⟩)) }}

end spec
end ConfChange
end EtcdGrove
end Perennial
