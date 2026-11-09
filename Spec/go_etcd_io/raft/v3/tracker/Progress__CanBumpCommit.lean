/-
## `Progress.CanBumpCommit(i)`

**Users.** `stepLeader`'s `MsgAppResp` (`raft.go:1570`: an empty append to tell the peer the
commit index): R2.

**Proof sketch.** Field reads. **Changes.** Over the model. **Margin.** None.
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

/-- Whether the peer should be told commit index `i`. -/
def Progress.CanBumpCommit.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"CanBumpCommit")) (Val #i))
  {{ RET #(P.canBumpCommit i); progressOwn p P }}

end spec
end Tracker
end EtcdGrove
end Perennial
