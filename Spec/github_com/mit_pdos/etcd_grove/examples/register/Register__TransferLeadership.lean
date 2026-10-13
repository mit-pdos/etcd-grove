/- Lean-first (no Rocq counterpart).

`(*Register).TransferLeadership(to)` (register.go), 2026-10-13: the replica's node is asked
to hand the leadership over to `to` (`Node.TransferLeadership`). Nothing is promised of the
outcome: the register's operations are specified whoever leads.
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
abbrev Register.TransferLeadership.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      isRegister γr γp r }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"TransferLeadership")) (Val #to))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
