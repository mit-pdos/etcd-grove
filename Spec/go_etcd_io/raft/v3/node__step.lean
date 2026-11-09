/-
## `node.step(ctx, m)` (internal)

`stepWithWaitOption(ctx, m, false)`. **Changes.** Mirrors the code.
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

/-- (internal) `stepWithWaitOption` with `wait = false`. -/
def node.step.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface)
    (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx ∗ msgPts ml (DFrac.own 1) m ∗
      stepOk n γ id m }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"step")) (Val #ctx)) (Val #ml))
  {{ (err : GoInterface), RET #err; propErr n ctx err }}

end spec
end Raft
end EtcdGrove
end Perennial
