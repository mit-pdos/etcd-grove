/-
## `(*RaftCluster).ValidateConfigurationChange(cc, shouldApplyV3)` (`cluster.go:306-391`): translated

**Users.** 2d's `applyConfChange`: a change refused here is applied to raft as a no-op (its node id
set to `None`) and answered with the error (the model's `clusterStep` refusals:
`peerURLExist`, `memberExist`, `memberNotFound`, `memberNotLearner`, `tooManyLearners`).

**Proof sketch.** `nil` at once when not `shouldApplyV3` (a replayed entry). Else the backend's
members and removed ids (`MustReadMembersFromBackend`, 4b: `beView`, read), then the checks by
type, the context unmarshalled where read (`json.Unmarshal`, trusted: `decodeCtx`,
`decodeMember`; a failure panics: `ccPanicFree`); an unknown type panics (`ccPanicFree`).

**Changes** (from `specs-ref`'s `RaftCluster__ValidateConfigurationChange.lean`): the outcome as a
relation (`ccResult`) over the backend's view.

**Margin.** Exact, up to the learner limit (`tooManyLearners` or not).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.raft.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **Validates a conf change** against the backend's members: the outcome `ccResult`. -/
def RaftCluster.ValidateConfigurationChange.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (p : Loc) (dq : DFrac) (cc : Raft.ConfChangeV1)
    (apply : Bool) (stb : ClusterSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ beView c stb ∗
      Raft.confChangePts (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #p)
        dq (.v1 cc) ∗ ⌜apply = true → ccPanicFree cc⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"ValidateConfigurationChange")) (Val #p)) (Val #apply))
  {{ (err : GoInterface), RET #err; beView c stb ∗
      Raft.confChangePts (interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfChange.ty) #p)
        dq (.v1 cc) ∗
      (⌜apply = false ∧ err = GoInterface.nil⌝ ∨
       ⌜apply = true ∧ ∃ r, ccResult stb cc r ∧
          err = (match r with | none => GoInterface.nil | some e => vErr e)⌝) }}

end spec

end Membership
end EtcdGrove
end Perennial
