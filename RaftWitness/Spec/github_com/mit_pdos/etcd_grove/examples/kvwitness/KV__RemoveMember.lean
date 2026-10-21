/- Lean-first (no Rocq counterpart).

`(*KV).RemoveMember(id)` (kv.go), 2026-10-15 (stage N): the replica's node is asked
to propose removing replica `id` from the cluster's voters (`Node.ProposeConfChange` of
`pb.ConfChange{Type: ConfChangeRemoveNode, NodeID: id}`, `rmCC id`). The change must be one the
cluster admits (`CCAllowed`: raft's `reCCOk`, which the cluster fixes at allocation; a cluster
of the store applies its conf changes with a decoder of the entry alone, `KVCC`). Nothing is
promised of the outcome: raft drops a change proposed while another one is not applied, and the
store's operations are specified whatever the configuration.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.RemoveMember.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64),
  CCAllowed γr.raft (.v1 (rmCC id)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗
      isKV γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"RemoveMember")) (Val #id))
  {{ RET #(); True }}

end spec

end kvwitness
end EtcdGrove
end Perennial
