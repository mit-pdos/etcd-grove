/- Lean-first (no Rocq counterpart).

## `node.step(ctx, m)` (node.go:498)

`stepWithWaitOption(ctx, m, false)`, for a message from the network.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.step.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (m : raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗ stepP γ id m }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"step"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #m))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
