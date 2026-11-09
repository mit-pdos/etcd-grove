/-
## `Progress.BecomeSnapshot(i)`

**Users.** `maybeSendSnapshot` (`raft.go:686`): R2. Snippet `raftconf/tracker.go`
(`ReqProgressFlow`).

**Proof sketch.** `ResetState(StateSnapshot)`; the pending snapshot, `Next`, `sentCommit`.
**Changes.** Over the model. **Margin.** None.
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

/-- Waits for snapshot `i` to be applied by the peer. -/
def Progress.BecomeSnapshot.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"BecomeSnapshot")) (Val #i))
  {{ RET #(); progressOwn p (P.becomeSnapshot i) }}

end spec
end Tracker
end EtcdGrove
end Perennial
