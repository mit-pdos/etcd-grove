/-
`filterNoDelete(e)` (`watch.go`): mvcc's filter for `NODELETE` (true drops the event).

**Users.** As `filterNoPut`'s: built by `FiltersFromRequest`, called by mvcc's `watcher.send` (3f).

**Proof sketch.** Reads `e.Type`.

**Changes** from `specs-ref`'s file: over the event's `Type` field instead of `mvcc.evIs`.

**Margin.** Mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`filterNoDelete(e)`**: the event is a delete (`Type` `1`). -/
def filterNoDelete.spec : Prop :=
  ∀ (e : Loc) (t : w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      e.[mvccpb.Event, go!"Type"] ↦{dq} t }}
    (App (Val (@! v3rpc.filterNoDelete)) (Val #e))
  {{ (b : Bool), RET #b; ⌜b = decide (t = W32 1)⌝ ∗ e.[mvccpb.Event, go!"Type"] ↦{dq} t }}

end spec

end V3rpc
end EtcdGrove
end Perennial
