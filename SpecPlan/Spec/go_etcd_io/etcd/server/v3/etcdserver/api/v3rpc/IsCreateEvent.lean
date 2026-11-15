/-
`IsCreateEvent(e)` (`watch.go`): the event is a key's creation.

**Users.** `sendLoop`'s `sendWatch` (`watch.go:448`: no previous key-value is looked up for a
creation). Exported, no other caller in the pinned sources.

**Proof sketch.** Reads `e.Type`, and for a put `e.Kv` (non-`nil`: the caller's) and its two
revisions.

**Changes** from `specs-ref`'s `IsCreateEvent.lean`: over the event's fields (any fractions: mvcc's
events have their own struct and a shared, read-only `Kv`), not mvcc's internal event record.

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

/-- **`IsCreateEvent(e)`**: a put (`Type` `0`) whose `Kv`'s create and mod revisions agree. -/
def IsCreateEvent.spec : Prop :=
  ∀ (e kv : Loc) (t : w32) (cr mr : w64) (dq dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      e.[mvccpb.Event, go!"Type"] ↦{dq} t ∗ e.[mvccpb.Event, go!"Kv"] ↦{dq} kv ∗
      kv.[mvccpb.KeyValue, go!"CreateRevision"] ↦{dk} cr ∗
      kv.[mvccpb.KeyValue, go!"ModRevision"] ↦{dk} mr }}
    (App (Val (@! v3rpc.IsCreateEvent)) (Val #e))
  {{ (b : Bool), RET #b; ⌜b = decide (t = W32 0 ∧ cr = mr)⌝ ∗
      e.[mvccpb.Event, go!"Type"] ↦{dq} t ∗ e.[mvccpb.Event, go!"Kv"] ↦{dq} kv ∗
      kv.[mvccpb.KeyValue, go!"CreateRevision"] ↦{dk} cr ∗
      kv.[mvccpb.KeyValue, go!"ModRevision"] ↦{dk} mr }}

end spec

end V3rpc
end EtcdGrove
end Perennial
