/- Lean-first (no Rocq counterpart).

`(*KV).RemoveMember(id)` (kv.go), 2026-10-15 (stage N): the replica's node is asked
to propose removing replica `id` from the cluster's voters (`Node.ProposeConfChange` of
`pb.ConfChange{Type: ConfChangeRemoveNode, NodeID: id}`, `rmCC id`), with the update raft's draft
API takes (`kv_ccAu`: the change's entry carries no datum, so the store does not move). Nothing is
promised of the outcome.

**Premise (2026-10-27): the change keeps the voters** (`RmShrink id`: a `CCShrink` of `kvVoters`,
so `id` is not a voter -- removing it drops at most a learner). Since 2026-10-28 (stage U4a) the
store runs over raft's cluster with snapshots and reconfiguration (`kvCluster`: `isCluster`, its
conf entries decided by the store's rule `kvRule`); `run` applies every committed conf change
(`node.ApplyConfChange.unifiedSpec`), and the premise is what keeps each decision at the voters'
membership (`kvMembership_rm`), which the store's snapshots (`kvSnapInv`, at `kvMembership`) and
its fixed voters (`Storage.voters`) assume. The premise is unsatisfiable for a voter, which is
what `RemoveMember` is for in Go (`TestRemoveMember` removes replica 3): the spec covers only the
calls that leave the voters as they are. Removing a voter needs the store to follow a changing
membership (its snapshots' `ConfState`, its voters).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.RemoveMember.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64),
  RmShrink id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isKV γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"RemoveMember")) (Val #id))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
