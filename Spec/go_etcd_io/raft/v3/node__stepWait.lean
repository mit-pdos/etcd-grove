/-
## `node.stepWait(ctx, m)` (internal)

`stepWithWaitOption(ctx, m, true)`. **Changes.** Mirrors the code.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- (internal) `stepWithWaitOption` with `wait = true`. -/
def node.stepWait.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ context.isContext ctx cd ∗ msgPts ml (DFrac.own 1) m ∗
      stepOk n γ id m }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"stepWait")) (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; propErr n err }}

end spec
end Raft
end EtcdGrove
end Perennial
