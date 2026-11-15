/-
## `(*streamReader).start()`

**Users.** `startPeer` (twice).

**Proof sketch.** `done`, `errorc` from the transport, `context.WithCancel(Background)`, the fork of `run` with `srRun`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

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

/-- (internal) **Starts a stream reader** (its `run` goroutine). -/
def streamReader.start.spec : Prop :=
  ∀ (cr : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ srFresh cr ν lid pid }}
    (App (Val (cr @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader.ty @!! go!"start")) (Val #()))
  {{ RET #(); srAt cr ν lid pid ∗ srStopRight cr }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
