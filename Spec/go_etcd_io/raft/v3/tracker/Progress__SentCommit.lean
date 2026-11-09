/-
## `Progress.SentCommit(c)`

**Users.** `maybeSendAppend` (`raft.go:660`), `sendHeartbeat` (`raft.go:709`): R2.

**Proof sketch.** A field write. **Changes.** Over the model. **Margin.** None.
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

/-- Records that commit index `c` was sent. -/
def Progress.SentCommit.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"SentCommit")) (Val #c))
  {{ RET #(); progressOwn p { P with sentCommit := c } }}

end spec
end Tracker
end EtcdGrove
end Perennial
