/-
## `(*streamWriter).stop()`

**Users.** `peer.stop`.

**Proof sketch.** `close(stopc)`, a receive on `done`.

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

/-- (internal) Stops the loop and waits for it. -/
def streamWriter.stop.spec : Prop :=
  ∀ (cw : Loc) (ν : Net GF) (lid pid : w64) (K : Msg → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ swAt cw ν lid pid K ∗ swStopRight cw }}
    (App (Val (cw @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
