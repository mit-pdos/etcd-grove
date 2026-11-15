/-
## `(*streamType).String()`

**Users.** logs: the stream reader's and writer's log lines call it on a local or a field (`t.String()`, `conn.t.String()`: Goose's pointer receiver; `stream.go`).

**Proof sketch.** Load `*p`, then `streamType.String.spec`.

**Changes.** verify-round (A8 completeness S1): restored from `specs-ref`'s `streamType__String_ptr.lean` (dropped in batch 2f, though the translated stream code calls it), unchanged.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A name for logs, through a pointer to the stream type. -/
def streamType.String_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ p ↦{dq} t }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} t }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
