/- Lean-first (no Rocq counterpart).

`(*KV).RemoveMember(id)` (kv.go), 2026-10-15 (stage N): the replica's node is asked
to propose removing replica `id` from the cluster's voters (`Node.ProposeConfChange` of
`pb.ConfChange{Type: ConfChangeRemoveNode, NodeID: id}`, `rmCC id`), with the update raft's draft
API takes (`kv_ccAu`: the change's entry carries no datum, so the store does not move). Nothing is
promised of the outcome: the store's static cluster admits no change (`Draft.isStaticCluster`), so
the update never fires.
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isKV γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"RemoveMember")) (Val #id))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
