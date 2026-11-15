/-
## `Inflights.Full()`

**Users.** `maybeSendAppend` (`raft.go:639`: no entries to a full replicating peer), `SentEntries`
(the flow pause): R2. Snippet `raftconf/tracker.go` (`ReqInflightsFull`).

**Proof sketch.** Field reads. **Changes.** Over the model's `full`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.tracker.Api

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

/-- Whether the ring is full (messages or bytes). -/
def Inflights.Full.spec : Prop :=
  ∀ (p : Loc) (I : InflightsV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ inflightsOwn p I }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Inflights.ty @!! go!"Full")) (Val #()))
  {{ RET #I.full; inflightsOwn p I }}

end spec
end Tracker
end EtcdGrove
end Perennial
