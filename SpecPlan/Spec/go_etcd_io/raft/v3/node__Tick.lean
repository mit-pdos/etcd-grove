/-
## `node.Tick()`

**Users.** etcd's `raftNode.tick` (`raft.go:163`, under `tickMu`), `advanceTicks`; the examples'
tickers (`kvdurable/kv.go:360`). Snippet: `readyloop.go`.

**Proof sketch.** A non-blocking send on the buffered `tickc` (the run goroutine calls
`RawNode.Tick`), or `done`, or the default branch logs through the logger (`loggerOk`).

**Changes.** Unchanged. **Margin.** A tick may be dropped (the buffer full).
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

/-- **Ticks node `n`** (or drops the tick). Any thread, any time. -/
def node.Tick.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Tick")) (Val #()))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
