/- Lean-first (no Rocq counterpart).

`(*Register).RemoveMember(id)` (register.go), 2026-10-15 (stage N): the replica's node is asked
to propose removing replica `id` from the cluster's voters (`Node.ProposeConfChange` of
`pb.ConfChange{Type: ConfChangeRemoveNode, NodeID: id}`, `rmCC id`). The change must be one the
cluster admits (`CCAllowed`: raft's `reCCOk`, which the cluster fixes at allocation; a cluster
of the register applies its conf changes with a decoder of the entry alone, `RegCC`). Nothing is
promised of the outcome: raft drops a change proposed while another one is not applied, and the
register's operations are specified whatever the configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Register.RemoveMember.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64),
  CCAllowed γr.raft (.v1 (rmCC id)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      isRegister γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"RemoveMember")) (Val #id))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
