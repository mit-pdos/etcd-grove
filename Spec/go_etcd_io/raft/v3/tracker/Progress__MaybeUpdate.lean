/-
## `Progress.MaybeUpdate(n)`

**Users.** `stepLeader`'s `MsgAppResp` (`raft.go:1542`: the peer acknowledged `n`; R2's `Match` is
an index the peer acknowledged, from the response's `msgSent`; the leader's own entries come back
the same way, a self-addressed `MsgAppResp` after the write, `raft.go:862`): R2. Snippet `raftconf/tracker.go`
(`ReqProgressFlow`).

**Proof sketch.** Field reads and writes. **Changes.** Over the model. **Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- Raises the match index to `n` (and `Next` past it), unpausing; whether it rose. -/
def Progress.MaybeUpdate.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"MaybeUpdate")) (Val #n))
  {{ RET #(P.maybeUpdate n).2; progressOwn p (P.maybeUpdate n).1 }}

end spec
end Tracker
end EtcdGrove
end Perennial
