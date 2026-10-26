/- Lean-first (no Rocq counterpart).

## `node.step(ctx, m)` (node.go:498)

`stepWithWaitOption(ctx, m, false)`, for a message from the network. (2026-10-16, stage R7a: any
`nodeCtx ctx cd`, the error `nodeErr cd err`; `node__stepWithWaitOption.lean`.) (2026-10-16, stage
R5: `m` a
`*pb.Message`, `ml`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.step.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ml : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      nodeCtx ctx cd ∗
      stepP γ id ml }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"step"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
