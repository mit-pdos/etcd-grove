/-
`filterNoPut(e)` (`watch.go`): mvcc's filter for `NOPUT` (true drops the event).

**Users.** Built by `FiltersFromRequest` (`filterFuncs`), called by mvcc's `watcher.send` (3f) on
every event of a response of a watcher created with it: its spec is how v3rpc meets mvcc's filter
contract (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, `## from 2b`).

**Proof sketch.** Reads `e.Type`.

**Changes** from `specs-ref`'s file: over the event's `Type` field (any fraction) instead of mvcc's
internal event record (`mvcc.evIs`).

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

/-- **`filterNoPut(e)`**: the event is a put (`Type` `0`). -/
def filterNoPut.spec : Prop :=
  ∀ (e : Loc) (t : w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      e.[mvccpb.Event, go!"Type"] ↦{dq} t }}
    (App (Val (@! v3rpc.filterNoPut)) (Val #e))
  {{ (b : Bool), RET #b; ⌜b = decide (t = W32 0)⌝ ∗ e.[mvccpb.Event, go!"Type"] ↦{dq} t }}

end spec

end V3rpc
end EtcdGrove
end Perennial
