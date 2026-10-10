/- Lean-first (no Rocq counterpart).

`(*Register).apply(e)` (register.go:112): one committed entry, after the committed prefix
`ap` the replica applied (`runOwn`); a waiter of the entry's operation, if this replica
proposed it and the entry is the operation's first, gets the value after it (`waitP`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Register.apply.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc)
    (ap : List raftpb.Entry) (e : raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isReplica γr γp r id n st ∗ runOwn γr r ap ∗
      isCommitted γr.raft (ap ++ [e]) }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"apply")) (Val #e))
  {{ RET #(); runOwn γr r (ap ++ [e]) }}

end spec

end register
end EtcdGrove
end Perennial
