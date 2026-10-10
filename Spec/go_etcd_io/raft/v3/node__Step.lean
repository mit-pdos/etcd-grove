/- Lean-first (no Rocq counterpart).

## `node.Step(ctx, m)` (node.go:473)

A message from the network, from any goroutine: `step` of it, on `recvc`, which `run` steps
as `RawNode.Step` does (`netP`: what `RawNode.Step` takes, and a term within the budget).
A local message not from a local target is ignored; `netP`'s types are not local.
Specified for `context.Background()`.
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
variable [AllG GF]

/-- See the file header. -/
abbrev node.Step.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (m : raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗ netP γ id m }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #m))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
