/-
## `node.stepWithWaitOption(ctx, m, wait)` (internal)

**Users.** `node.step`, `node.stepWait`. **Proof sketch.** Non-proposals go on `recvc`; proposals on
`propc` (armed only with a leader), with a result channel when `wait`; `ctx` and `done` end the waits.
The `ctx` case: `ctx.Done()` by W0's requested `Context.Done.spec` (a channel, or `nil` for a context
never done, which no `select` case fires on), a receive on it by `Context.doneRecv.spec` (gives
`Context.ctxDone ctx`), then `ctx.Err()` by `Context.ErrDone.spec` (`notes/specs-only/req/context.md`,
"from R1"); hence `nodeErr`'s context arm. Every `node.*` spec taking a context rests on these.
The message and its `stepOk` go to the run goroutine. **Changes.** Mirrors the code.

**Integration I2.** The message is a received one (`msgRecv`: its `Entries` capacity owned, which
`raft.Step` hands to the log on a `MsgApp`) or an owned local message that is no `MsgApp` (R2's
`stepMsg`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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

/-- (internal) Hands `m` to the run goroutine. -/
def node.stepWithWaitOption.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface)
    (ml : Loc) (m : Msg) (wait : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx ∗
      (msgRecv ml m ∨ (msgPts ml (DFrac.own 1) m ∗ ⌜m.type ≠ MsgApp⌝)) ∗
      stepOk n γ id m }}
    (App (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"stepWithWaitOption")) (Val #ctx)) (Val #ml))
      (Val #wait))
  {{ (err : GoInterface), RET #err; propErr n ctx err }}

end spec
end Raft
end EtcdGrove
end Perennial
